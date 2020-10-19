import os
import re
from pathlib import Path
import sys
import threading
import time
from datetime import timedelta, date
from configparser import ConfigParser
import mimetypes
import random
import typing

# Getting base path of the script.
SCRIPT_DIRECTORY = os.path.join(os.path.dirname(__file__))

try:
    # noinspection PyUnresolvedReferences,PyUnboundLocalVariable
    octopusvariables
except:
    octopusvariables = False

if octopusvariables:
    # If running on Octopus, add the dependency package directory
    sys.path.append(
        octopusvariables["Octopus.Action.Package[UDPPythonDependencies].ExtractedPath"]
    )

import glob
import base64
import secrets
import json
import shutil
import zipfile
import uuid
from datetime import datetime as dt
import requests
from requests.auth import HTTPBasicAuth
from azure.common.credentials import ServicePrincipalCredentials

# Had to import a specific version of the management client to allow empty copies
# in the ARM templates.
from azure.mgmt.resource.resources import ResourceManagementClient
from azure.mgmt.resource.resources.v2018_05_01.models import DeploymentMode
from azure.core.exceptions import ResourceExistsError
from azure.common import AzureMissingResourceHttpError
from azure.common.client_factory import get_client_from_cli_profile
from azure.mgmt.storage import StorageManagementClient
from azure.mgmt.storage.models import StorageAccountCreateParameters, Sku
from azure.keyvault import KeyVaultClient
from azure.keyvault.v7_0.models.key_vault_error_py3 import KeyVaultErrorException
from azure.mgmt.keyvault import KeyVaultManagementClient
from azure.mgmt.sql import SqlManagementClient
from azure.mgmt.datafactory import DataFactoryManagementClient
from azure.mgmt.eventhub import EventHubManagementClient
from azure.mgmt.eventhub.models import Eventhub, EHNamespace, Sku, ErrorResponseException
from azure.cosmosdb.table.tableservice import TableService
from azure.storage.blob import BlobServiceClient, BlobAnalyticsLogging, Metrics, RetentionPolicy, generate_blob_sas, AccountSasPermissions, BlobSasPermissions, ContentSettings, StaticWebsite, ResourceTypes
from azure.storage.common.models import Logging
from azure.storage.queue import QueueServiceClient, QueueAnalyticsLogging
from azure.mgmt.web import WebSiteManagementClient, models as AzureWebModels
from azure.cosmos.cosmos_client import CosmosClient
from azure.cosmos.errors import HTTPFailure
from msrestazure.azure_exceptions import CloudError
import adal
from adal import AuthenticationContext
import logging
import pyodbc
from udp_utils.apigee import ApigeeClient
from udp_utils.databricks import DatabricksJob, DatabricksFS, DatabricksSecretClient, DatabricksWorkspace
from udp_utils.adls2 import DataLakeGen2Client
from .exceptions import SourceNameInUse, SQLFolderNotFound
from ..ingestion import types as ingestion_types
from .. import defaults

# Setting up logger
logger = logging.getLogger("udp")

# Setting logging level for ADAL library to WARN.
logging.getLogger("adal-python").setLevel(logging.WARN)
logging.getLogger("azure.storage").setLevel(logging.WARN)
logging.getLogger("azure.cosmosdb").setLevel(logging.WARN)
logging.getLogger("azure.storage.blob").setLevel(logging.WARN)
logging.getLogger("urllib3").setLevel(logging.WARN)
# Hide logging "errors" when creating a table that already exists
logging.getLogger("azure.cosmosdb.table.common.storageclient").setLevel(logging.CRITICAL)
logging.getLogger("azure.core.pipeline.policies.http_logging_policy").setLevel(logging.CRITICAL)


def add_years(d, years):
    """Return a date that's `years` years after the date (or datetime)
    object `d`. Return the same calendar date (month and day) in the
    destination year, if it exists, otherwise use the following day
    (thus changing February 29 to March 1).

    """
    try:
        return d.replace(year=d.year + years)
    except ValueError:
        return d + (date(d.year + years, 1, 1) - date(d.year, 1, 1))

class ResourceDeployer(object):
    """
    The UDP resource deployer class.

    The class contains all necessary methods to deploy the UDP infrastructure,
    both for individual applications and shared.

    Args:
        environment: The environment name for the deployer.
        resource_group: The Azure resource group name.
        org_name: The organization name for deployment.
        app_name: The application name for deployment.
        location: The Azure location to deploy to.

    Attributes:
        environment: The environment name for the deployer.
        resource_group: The Azure resource group name.
        org_name: The organization name for deployment.
        app_name: The application name for deployment.
        location: The Azure location to deploy to.
        region_code: The three-letter region code associated with the location.
        region: The global region code (AMER, EMEA, APAC)
    """

    def __init__(
        self,
        environment: str,
        resource_group: str,
        org_name: str,
        app_name: str,
        resource_tags: dict = dict(),
        location: str = defaults.LOCATION,
        dr_location: str = defaults.DR_LOCATION,
        lake_account_name: str = None,
        lake_account_key: str = None,
        app_path: str = None,
        app_build_path: str = None,
        udp_resource_group: str = None,
        alerting=None,
        libraries=None,
        app_ad_group_id=None,
        web_resource_group=None,
        config_path=None,
        apps_table_name=None,
        snapshot_table_name=None,
        build_output_dir=defaults.BUILD_OUTPUT_DIR,
        octopusvariables=False,
        singleAspFlag = False,
        email_receivers: typing.List[typing.Dict[str, str]] = list(),
        db_connection_timeout = int,
    ):

        region_code_map = {
            "centralus": "cus",
            "Central US": "cus",
            "central us": "cus",
            "eastus2": "eu2",
            "East US 2": "eu2",
            "east us 2": "eu2",
            "West Europe": "weu",
            "westeurope": "weu",
        }
        global_region_map = {
            "centralus": "amer",
            "Central US": "amer",
            "central us": "amer",
            "eastus2": "amer",
            "East US 2": "amer",
            "east us 2": "amer",
            "westeurope" : "europe",
        }
        if len(environment) > 3:
            self.environment = environment[-3:]
        else:
            self.environment = environment
        self.org_name = org_name
        self.location = location
        self.dr_location = dr_location
        self.region_code = region_code_map[location]
        self.dr_region_code = region_code_map[dr_location]
        self.region = global_region_map[location]
        self.app_name = app_name
        self.resource_group = resource_group
        self.snapshot_scheduler_jobs = []
        self.namespace_threads = []
        self.key_vault_threads = []
        self.source_threads = []
        self.data_store_threads = []
        self.api_threads = []
        self.batch_threads = []
        self.threads = []
        self.thread_exceptions = []
        if self.environment in ["dev", "uat", "prd"]:
            self.deploy_apigee = True

            # TODO: We originally sent the credentials in as "prod" - should change them to "prd"
            if self.environment == "prd":
                self.apigee_client_id = "udpapigeeclientidprod"
                self.apigee_client_secret = "udpapigeeclientsecretprod"
            else:
                self.apigee_client_id = "udpapigeeclientid{}".format(self.environment)
                self.apigee_client_secret = "udpapigeeclientsecret{}".format(
                    self.environment
                )
        else:
            self.deploy_apigee = False
            self.apigee_client_id = "udpapigeeclientid"
            self.apigee_client_secret = "udpapigeeclientsecret"
        self.resource_tags = resource_tags
        self.databricks_ad_token = None
        self.databricks_ad_token_prd = None
        self.databricks_token = None
        self.databricks_token_prd = None
        self.udp_resource_group = udp_resource_group
        self.core_role_group = "fe6beb49-7688-4643-9df0-c02a482ea339"
        self.alerting = alerting
        self.email_receivers: typing.List[typing.Dict[str, str]] = list()
        if self.alerting:
            failure_emails = self.alerting.get("failure_emails")
            if failure_emails:
                self.email_receivers.extend(
                    {
                        "name": email,
                        "emailAddress": email
                    } for email in failure_emails
                )
        self.libraries = libraries
        self.app_ad_group_id = app_ad_group_id
        self.source_table_name = "UDPSources"
        self.apps_table_name = "UDPApps"
        self.snapshot_table_name = "UDPSnapshots"
        self.config_path = config_path
        self.tenant = "bfef2b06-d256-4f8e-bd03-8d3687987063"
        if web_resource_group:
            self.web_resource_group = web_resource_group
        else:
            self.web_resource_group = resource_group

        self.singleAspFlag = singleAspFlag

        # Setting up network resource group. Dev and UAT share a resource group,
        # and prod has it's own. Sandboxes all use the same.
        if self.environment == "prd":
            self.network_resource_group = "JLL-GB-RG-Networking-APProd"
            self.vnet_name = "JLL-GB-VN-USCN-APProdDMZ-01"
        elif self.environment in ["dev", "uat"]:
            self.network_resource_group = "JLL-GB-RG-Networking-APDev"
            self.vnet_name = "JLL-GB-VN-USCN-APDevDMZ-01"
        else:
            self.network_resource_group = "JLL-SB-RG-UnifiedDataPlatform"
            self.vnet_name = "JLL-GB-VN-USCN-APSBDMZ-01"

        # These variables are used when running on the Octopus server.
        if octopusvariables:
            logger.info("Running on Octopus server.")

            self.template_base_path = octopusvariables[
                "Octopus.Action.Package[UDPARMTemplates].ExtractedPath"
            ]
            self.shared_functions_base_path = octopusvariables[
                "Octopus.Action.Package[UDPFunctions].ExtractedPath"
            ]
            self.dbup_path = octopusvariables[
                "Octopus.Action.Package[UDPDbUp].ExtractedPath"
            ]
            # This try/catch is for local testing of Octopus functionality.
            try:
                self.client_id = octopusvariables["SPApplicationID"]
                self.secret = octopusvariables["SPKey"]
                self.tenant = octopusvariables["SPKTenantID"]
                self.credentials = ServicePrincipalCredentials(
                    client_id=octopusvariables["SPApplicationID"],
                    secret=octopusvariables["SPKey"],
                    tenant=octopusvariables["SPKTenantID"],
                )
                self.key_vault_credentials = ServicePrincipalCredentials(
                    client_id=octopusvariables["SPApplicationID"],
                    secret=octopusvariables["SPKey"],
                    tenant=octopusvariables["SPKTenantID"],
                    resource="https://vault.azure.net",
                )
                self.subscription_id = octopusvariables["SubscriptionID"]
                self.client = ResourceManagementClient(
                    self.credentials, self.subscription_id
                )
                self.storage_client = StorageManagementClient(
                    self.credentials, self.subscription_id
                )
                self.eh_client = EventHubManagementClient(
                    self.credentials, self.subscription_id
                )
                self.web_client = WebSiteManagementClient(
                    self.credentials, self.subscription_id
                )
                self.sql_client = SqlManagementClient(
                    self.credentials, self.subscription_id
                )
                self.kv_client = KeyVaultClient(self.key_vault_credentials)
                self.adf_client = DataFactoryManagementClient(
                    self.credentials, self.subscription_id
                )
                self.kv_mgmt_client = KeyVaultManagementClient(
                    self.credentials, self.subscription_id
                )
                authority_uri = "https://login.microsoftonline.com/{}".format(
                    octopusvariables["SPKTenantID"]
                )
                context = adal.AuthenticationContext(authority_uri)
                resource_uri = "https://management.azure.com/"
                mgmt_token = context.acquire_token_with_client_credentials(
                    resource_uri,
                    octopusvariables["SPApplicationID"],
                    octopusvariables["SPKey"],
                )
                self.key_vault = "JLL-AM-KV-PaaS-FDprod01"
                self.key_vault_db = "JLL-AM-KV-DBA-FDprod01"
                apigee_credentials = ServicePrincipalCredentials(
                    client_id=octopusvariables["SPApplicationID"],
                    secret=octopusvariables["SPKey"],
                    tenant=octopusvariables["SPKTenantID"],
                )
                self.apigee_client = ApigeeClient(
                    self.key_vault,
                    self.apigee_client_id,
                    self.apigee_client_secret,
                    az_credentials=apigee_credentials,
                    env=self.environment,
                )
            except KeyError:
                self.client = get_client_from_cli_profile(ResourceManagementClient)
                self.storage_client = get_client_from_cli_profile(
                    StorageManagementClient
                )
                self.eh_client = get_client_from_cli_profile(EventHubManagementClient)
                self.web_client = get_client_from_cli_profile(WebSiteManagementClient)
                self.kv_client = get_client_from_cli_profile(KeyVaultClient)
                self.adf_client = get_client_from_cli_profile(DataFactoryManagementClient)
                self.kv_mgmt_client = get_client_from_cli_profile(
                    KeyVaultManagementClient
                )
                self.sql_client = get_client_from_cli_profile(SqlManagementClient)
                self.key_vault = "jllcuskvudpsb"
                self.key_vault_db = "jllcuskvudpsb"
                self.apigee_client = ApigeeClient(
                    self.key_vault,
                    self.apigee_client_id,
                    self.apigee_client_secret,
                    env=self.environment,
                )
                self.subscription_id = self.client.resources.config.subscription_id

            self.cosmos_client = None

            self.api_path = octopusvariables[
                "Octopus.Action.Package[udp.api].ExtractedPath"
            ]
            self.real_time_path = octopusvariables[
                "Octopus.Action.Package[udp.realtime].ExtractedPath"
            ]
            try:
                self.batch_path = octopusvariables[
                    "Octopus.Action.Package[udp.batch].ExtractedPath"
                ]
            except KeyError:
                self.batch_path = None
            self.sql_path = octopusvariables[
                "Octopus.Action.Package[udp.sql].ExtractedPath"
            ]
            try:
                self.web_path = octopusvariables[
                    "Octopus.Action.Package[udp.web].ExtractedPath"
                ]
            except KeyError:
                self.web_path = None
            try:
                self.python_lib_path = octopusvariables[
                    "Octopus.Action.Package[udp.python_lib].ExtractedPath"
                ]
            except KeyError:
                self.python_lib_path = None
            try:
                self.udp_utils_path = glob.glob(
                    "{}/udp_utils-*.*.*-py3-none-any.whl".format(
                        octopusvariables[
                            "Octopus.Action.Package[udp.utils].ExtractedPath"
                        ]
                    )
                )[0]
            except KeyError:
                raise Exception("Could not find udp-utils package.")
            if self.environment in ["prd", "uat", "sit", "dev"]:
                # Set Key Vault based on environment.
                self.key_vault_env = self.environment
                # If in a standard environment, we'll do blue-green deployments.
                # This will require checking which instance (blue or green)
                # is currently running.
                # We'll try blue.
                blue = "{}-b".format(self.resource_group)
                green = "{}-g".format(self.resource_group)
                blue_exists = self.client.resource_groups.check_existence(blue)
                # If it exists, we'll deploy to green.
                if blue_exists:
                    self.compute_resource_group = green
                    self.compute_environment = "{}-g".format(self.environment)
                # Else deploy to blue.
                else:
                    self.compute_resource_group = blue
                    self.compute_environment = "{}-b".format(self.environment)

                # NOTE: Blue-green deployments are still under development.
                # Consider this a feature flag turning them off.
                # TODO: Fix incompatibility of blue-green deployments with linux
                # ASPs deployed under Web RG.
                self.compute_resource_group = self.resource_group
                self.compute_environment = self.environment
            else:
                # If Key Vault doesn't match an environment tag, it's assumed to
                # be a test environment.
                self.key_vault_env = "sbx"
                self.compute_resource_group = self.resource_group
                self.compute_environment = self.environment
            self.databricks_key_name = "udpdatabrickskey{}".format(self.key_vault_env)

        # These variables are used when an application path is specified.
        elif app_path:
            self.build_output_dir = build_output_dir
            self.template_base_path = "{}/../../arm_templates/".format(SCRIPT_DIRECTORY)
            self.shared_functions_base_path = self.build_output_dir
            self.client = get_client_from_cli_profile(ResourceManagementClient)
            self.storage_client = get_client_from_cli_profile(StorageManagementClient)
            self.eh_client = get_client_from_cli_profile(EventHubManagementClient)
            self.web_client = get_client_from_cli_profile(WebSiteManagementClient)
            self.kv_client = get_client_from_cli_profile(KeyVaultClient)
            self.adf_client = get_client_from_cli_profile(DataFactoryManagementClient)
            self.kv_mgmt_client = get_client_from_cli_profile(KeyVaultManagementClient)
            self.sql_client = get_client_from_cli_profile(SqlManagementClient)
            self.dbup_path = "{}/dbup".format(self.build_output_dir)
            self.api_path = "{}/api_layer".format(app_build_path)
            self.real_time_path = "{}/real_time".format(app_build_path)
            self.batch_path = "{}/batch".format(app_path)
            self.sql_path = "{}/sql".format(app_path)
            self.web_path = "{}/web".format(app_build_path)
            self.python_lib_path = "{}/python_lib".format(app_build_path)
            try:
                utils_path = f"{self.build_output_dir}/udp_utils/udp_utils-*.*.*-py3-none-any.whl"
                self.udp_utils_path = glob.glob(utils_path)[0]
            except IndexError:
                logger.error(
                    "Could not find UDP utils wheel. Have you run the build script recently?"
                )
                exit(1)
            self.subscription_id = self.client.resources.config.subscription_id
            self.key_vault = "jllcuskvudpsb"
            self.key_vault_db = "jllcuskvudpsb"
            self.databricks_key_name = "udpdatabrickskey"
            self.key_vault_env = "sbx"
            # self.apigee_client = ApigeeClient(
            #     self.key_vault,
            #     self.apigee_client_id,
            #     self.apigee_client_secret,
            #     env=self.environment,
            # )
            # No need to do blue-green deployments when running locally.
            self.compute_resource_group = self.resource_group
            self.compute_environment = self.environment

        # These variables are used when running with one of the UDP test applications.
        else:
            self.build_output_dir = build_output_dir
            self.template_base_path = "{}/../../arm_templates/".format(SCRIPT_DIRECTORY)
            self.shared_functions_base_path = self.build_output_dir
            self.client = get_client_from_cli_profile(ResourceManagementClient)
            self.storage_client = get_client_from_cli_profile(StorageManagementClient)
            self.eh_client = get_client_from_cli_profile(EventHubManagementClient)
            self.web_client = get_client_from_cli_profile(WebSiteManagementClient)
            self.kv_client = get_client_from_cli_profile(KeyVaultClient)
            self.adf_client = get_client_from_cli_profile(DataFactoryManagementClient)
            self.kv_mgmt_client = get_client_from_cli_profile(KeyVaultManagementClient)
            self.sql_client = get_client_from_cli_profile(SqlManagementClient)
            self.dbup_path = "{}/dbup".format(self.build_output_dir)
            self.api_path = "{}/api_layer".format(app_build_path)
            self.real_time_path = "{}/real_time".format(app_build_path)
            self.batch_path = "{}/batch".format(app_path)
            self.sql_path = "{}/sql".format(app_path)
            self.web_path = "{}/web".format(app_build_path)
            self.python_lib_path = "{}/python_lib".format(app_build_path)
            try:
                utils_path = f"{self.build_output_dir}/udp_utils/udp_utils-*.*.*-py3-none-any.whl"
                self.udp_utils_path = glob.glob(utils_path)[0]
            except IndexError:
                logger.error(
                    "Could not find UDP utils wheel. Have you run the build script recently?"
                )
                exit(1)
            self.subscription_id = self.client.resources.config.subscription_id
            self.key_vault = "jllcuskvudpsb"
            self.key_vault_db = "jllcuskvudpsb"
            self.databricks_key_name = "udpdatabrickskey"
            self.key_vault_env = "sbx"
            # self.apigee_client = ApigeeClient(self.key_vault, "udpapigeeclientid", "udpapigeeclientsecret", env=self.environment)
            # No need to do blue-green deployments when running locally.
            self.compute_resource_group = self.resource_group
            self.compute_environment = self.environment

        self.azure_key_vault = "{0}-{1}-kv-{2}-{3}".format(
            self.org_name, self.region_code, self.app_name, self.environment
        )
        self.azure_key_vault_dr = "{0}-{1}-kv-{2}-{3}".format(
            self.org_name, self.dr_region_code, self.app_name, self.environment
        )
        # Check if azure key vault is new or existing
        try:
            response = self.kv_mgmt_client.vaults.get(
                self.resource_group, self.azure_key_vault
            )
            if response:
                self.azure_key_vault_new_or_existing = "existing"
        except CloudError as e:
            self.azure_key_vault_new_or_existing = "new"

        self.real_time_server = None
        self.real_time_database = None
        self.sql_databases = None
        self.real_time_user = None
        self.real_time_password = None
        self.cosmos_url = None
        self.cosmos_key = None
        self.cosmos_key_read_only = None
        self.search_name = None
        self.parameters_object: typing.Dict[str, typing.Any] = {
            "environment": {"value": self.environment},
            "orgName": {"value": self.org_name},
            "projectName": {"value": self.app_name.replace("_", "")},
            "location": {"value" : self.location},
            "regionCode" : {"value": self.region_code},
            "projectInformation": {
                "value": {
                    **self.resource_tags,
                    **{
                        "AppName": self.app_name.replace("_", ""),
                        "Environment": self.environment,
                    },
                }
            },
        }
        self.dr_environments = []
        self.dr_flag = self.environment in self.dr_environments
        self.event_hub_namespaces = []
        self.event_hubs = []
        self.consumer_groups = []
        self.source_list = []

        # If the storage account key and name aren't passed, retrieve them.
        # If the app name is "udp", then it's assumed to be deployment of main infrastructure,
        # and the lake doesn't exist yet.
        if not (lake_account_name and lake_account_key) and self.app_name != "udp":
            logger.info(
                "Data lake account name and key not specified. Using default name and getting key."
            )
            self.lake_account_name = "{}{}adlsudp{}".format(
                self.org_name, self.region_code, self.environment
            )
            storage_keys = self.storage_client.storage_accounts.list_keys(
                self.udp_resource_group, self.lake_account_name
            )
            storage_keys = {v.key_name: v.value for v in storage_keys.keys}
            self.lake_account_key = storage_keys["key1"]
            self.table_service = TableService(
                account_name=self.lake_account_name, account_key=self.lake_account_key
            )
        elif (lake_account_name and lake_account_key) and self.app_name != "udp":
            self.lake_account_name = lake_account_name
            self.lake_account_key = lake_account_key
            self.table_service = TableService(
                account_name=self.lake_account_name, account_key=self.lake_account_key
            )
        else:
            logger.info(
                "Main deployment detected for app 'udp'. Ignoring lake information retrieval."
            )
            self.lake_account_name = None
            self.lake_account_key = None
            self.table_service = None

        self.mdm_client_id = self.kv_client.get_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.key_vault
            ),
            self.apigee_client_id,
            "",
        ).value
        self.mdm_client_secret = self.kv_client.get_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.key_vault
            ),
            self.apigee_client_secret,
            "",
        ).value

        # Initial flags set to false for component deployment.
        self.sql_flag = False
        self.search_flag = False
        self.signalr_flag = False
        self.cosmos_flag = False

        logger.info("Getting app service principal info from vault.")
        try:
            self.app_client_id = self.kv_client.get_secret(
                f"https://{self.key_vault}.vault.azure.net",
                f"udpappclientid{self.app_name}{self.key_vault_env}",
                "",
            ).value
            self.app_object_id = self.kv_client.get_secret(
                f"https://{self.key_vault}.vault.azure.net",
                f"udpappobjectid{self.app_name}{self.key_vault_env}",
                "",
            ).value
            self.app_client_secret = self.kv_client.get_secret(
                f"https://{self.key_vault}.vault.azure.net",
                f"udpappclientsecret{self.app_name}{self.key_vault_env}",
                "",
            ).value
        except KeyVaultErrorException:
            logger.warning(
                f"Service principal credentials were not found for {self.app_name} in {self.key_vault_env}."
                f" Lake Key access will be depreciated in a future release."
            )
            self.app_client_id = None
            self.app_object_id = None
            self.app_client_secret = None

    def get_directory_size(self, directory):
        """Returns the `directory` size in bytes."""
        total = 0
        try:
            # print("[+] Getting the size of", directory)
            for entry in os.scandir(directory):
                if entry.is_file():
                    # if it's a file, use stat() function
                    total += entry.stat().st_size
                elif entry.is_dir():
                    # if it's a directory, recursively call this function
                    total += self.get_directory_size(entry.path)
        except NotADirectoryError:
            # if `directory` isn't a directory, get the file size then
            return os.path.getsize(directory)
        except PermissionError:
            # if for whatever reason we can't open the folder, return 0
            return 0
        return total

    def get_subdir_sizes(self, start_dir):
        logger.info(f"File sizes for path {start_dir}:")
        dirs = [ name for name in os.listdir(start_dir) if os.path.isdir(os.path.join(start_dir, name)) ]
        for d in dirs:
            size = self.get_directory_size(Path(start_dir, d))
            logger.info(f"{d}: {size}")

    @staticmethod
    def zip_dir(folder: str):
        """
        Zip a given directory into a zip file in place.

        Args:
            folder: The directory to zip.
        """
        # Make sure folder is absolute.
        folder = os.path.abspath(folder)
        name = os.path.basename(folder)
        zip_file = zipfile.ZipFile(f'{folder.rstrip("/")}.zip', 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=4)

        zip_file.write(folder, arcname=os.path.basename(folder))


        # Walk the entire folder tree and compress the files in each folder.
        for foldername, subfolders, filenames in os.walk(folder):

            # Add the current folder to the ZIP file if not root folder
            if foldername != folder:
                rel_path = os.path.relpath(foldername, folder)
                zip_file.write(foldername, arcname=rel_path)

            # Add all the files in this folder to the ZIP file.
            for filename in filenames:
                rel_path = os.path.relpath(foldername, folder)
                zip_file.write(os.path.join(foldername, filename), arcname=os.path.join(rel_path, filename))
        zip_file.close()

    def get_databricks_ad_token(self):
        """
        Get an AD token for Databricks.
        """
        if not self.databricks_ad_token:
            authority_host_url = "https://login.microsoftonline.com/"
            databricks_resource_id = "2ff814a6-3304-4ab8-85cb-cd0e6f879c1d"
            authority_url = authority_host_url + self.tenant
            context = AuthenticationContext(authority_url)
            svc_password = self.kv_client.get_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.key_vault
                ),
                "udpsvcazdatabricks",
                "",
            ).value
            token_response = context.acquire_token_with_username_password(
                databricks_resource_id,
                "Svc.Azdatabricks@jll.com",
                svc_password,
                "88020156-f114-4462-8eb3-0a3cbd55a7c9",
            )
            self.databricks_ad_token = token_response["accessToken"]

        return self.databricks_ad_token

    def get_databricks_header(self, workspace: str):
        """
        Create the Databricks auth header for a workspace.

        Args:
            workspace: The name of the workspace for which to retrieve a token.
        """
        token = self.get_databricks_ad_token()
        db_resource_id = "/subscriptions/{}/resourceGroups/{}/providers/Microsoft.Databricks/workspaces/{}".format(
            self.subscription_id, self.compute_resource_group, workspace
        )
        header = {
            "Authorization": "Bearer " + token,
            "X-Databricks-Azure-Workspace-Resource-Id": db_resource_id,
        }
        return header

    def get_databricks_header_prd(self, workspace: str, env_token: str):
        """
        Create the Databricks auth header for a workspace.

        Args:
            workspace: The name of the workspace for which to retrieve a token.
        """
        if env_token in ["uat" , "dev"]:
            self.subscription_id_env = "b01ac92a-0faf-4fd4-9dc5-2506afa98816"
        else:
            self.subscription_id_env = '7b775d22-9953-4246-ac42-63664f9cfa8e'
        if self.environment in ["prd", "uat", "dev"]:
            self.compute_resource_group_env = self.compute_resource_group[:-3] + env_token
        else:
            self.compute_resource_group_env = 'JLL-GB-RG-UnifiedDataPlatform-test-prd'

        token = self.get_databricks_ad_token()
        db_resource_id = "/subscriptions/{}/resourceGroups/{}/providers/Microsoft.Databricks/workspaces/{}".format(
            self.subscription_id_env, self.compute_resource_group_env, workspace
        )
        header_prd = {
            "Authorization": "Bearer " + token,
            "X-Databricks-Azure-Workspace-Resource-Id": db_resource_id,
        }
        return header_prd

    def create_databricks_token(self, workspace: str):
        """
        Either retrieve or create a Databricks API token.

        Args:
            workspace: The name of the workspace for which to retrieve a token.
        """
        header = self.get_databricks_header(workspace)

        logger.info("Creating Databricks API token.")
        create_response = requests.post(
            "https://{}.azuredatabricks.net/api/2.0/token/create".format(self.location),
            headers=header,
        )
        if not create_response.ok:
          
            logger.error(create_response.text)
            create_response.raise_for_status()

        logger.info("Checking existing Databricks tokens and removing old ones.")
        token_response = requests.get(
            "https://{}.azuredatabricks.net/api/2.0/token/list".format(self.location),
            headers=header,
        )
        if not token_response.ok:
            logger.error(token_response.text)
            token_response.raise_for_status()

        tokens = token_response.json()["token_infos"]
        if len(tokens) > 3:
            logger.info(
                "Found more than three Databricks tokens. Removing the oldest tokens."
            )

            # Delete every token except for the most recent three
            list.sort(tokens, key=lambda x: x["creation_time"])
            for delete_token in tokens[:-3]:
                revoke_response = requests.post(
                    "https://{}.azuredatabricks.net/api/2.0/token/delete".format(
                        self.location
                    ),
                    headers=header,
                    json={"token_id": delete_token["token_id"]},
                )

        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "databricks-token",
            create_response.json()["token_value"],
        )

        if self.dr_flag:
            self.kv_client.set_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault_dr
                ),
                "databricks-token",
                create_response.json()["token_value"],
            )

        return create_response.json()["token_value"]

    def create_databricks_token_prd(self, workspace: str):
        """
        Either retrieve or create a Databricks API token.

        Args:
            workspace: The name of the workspace for which to retrieve a token.
        """
        env_token = "prd"
        header = self.get_databricks_header_prd(workspace, env_token)

        logger.info("Creating Databricks API token.")
        create_response = requests.post(
            "https://{}.azuredatabricks.net/api/2.0/token/create".format(self.location),
            headers=header,
        )
        if not create_response.ok:
            env_token = "uat"
            workspace_name = workspace[:-3] + env_token
            header = self.get_databricks_header_prd(workspace_name, env_token)
            create_response = requests.post(
            "https://{}.azuredatabricks.net/api/2.0/token/create".format(self.location),
            headers=header,
            )
            if not create_response.ok:
                env_token = "dev"
                workspace_name = workspace[:-3] + env_token
                header = self.get_databricks_header_prd(workspace_name, env_token)
                create_response = requests.post(
                "https://{}.azuredatabricks.net/api/2.0/token/create".format(self.location),
                headers=header,
                )
                logger.error(create_response.text)
                create_response.raise_for_status()

        logger.info("Checking existing Databricks tokens and removing old ones.")
        token_response = requests.get(
            "https://{}.azuredatabricks.net/api/2.0/token/list".format(self.location),
            headers=header,
        )
        if not token_response.ok:
            logger.error(token_response.text)
            token_response.raise_for_status()

        tokens = token_response.json()["token_infos"]
        if len(tokens) > 3:
            logger.info(
                "Found more than three Databricks tokens. Removing the oldest tokens."
            )

            # Delete every token except for the most recent three
            list.sort(tokens, key=lambda x: x["creation_time"])
            for delete_token in tokens[:-3]:
                revoke_response = requests.post(
                    "https://{}.azuredatabricks.net/api/2.0/token/delete".format(
                        self.location
                    ),
                    headers=header,
                    json={"token_id": delete_token["token_id"]},
                )

        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "databricks-disco-token",
            create_response.json()["token_value"],
        )

        if self.dr_flag:
            self.kv_client.set_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault_dr
                ),
                "databricks-disco-token",
                create_response.json()["token_value"],
            )

        return create_response.json()["token_value"]


    def get_or_generate_sql_password(
        self,
        key_vault_name: str,
        secret_name: str,
        set_secret: bool = False
    ):
        try:
            sql_password = self.kv_client.get_secret(
                f"https://{key_vault_name}.vault.azure.net",
                secret_name,
                "",
            ).value
            logger.info(f"Found SQL password with secret name {secret_name} in the {key_vault_name} vault.")

        # Apparently the Azure library errors don't inherit the BaseException class,
        # so catching a generic exception and checking.
        except Exception as e:
            # If the Key Vault doesn't exist or the secret isn't in there, generate
            # a new one.
            if isinstance(e.inner_exception, requests.exceptions.ConnectionError) or e.error.error.code == "SecretNotFound":
                logger.info("Generating random SQL password.")
                # Randomly generate a password for the server.
                password_characters = "abcdefghijklmnopqrstuvwxyz01234567890ABCDEFGHIJKLMNOPQRSTUVWXYZ#%^&.<>|~"
                passlen = 16
                sql_password =  "".join(random.sample(password_characters, passlen))

                if set_secret:
                    logger.info(f"Vaulting the {secret_name} secret in the {key_vault_name} vault.")
                    self.kv_client.set_secret(
                        f"https://{key_vault_name}.vault.azure.net",
                        secret_name,
                        sql_password
                    )
            else:
                raise e

        return sql_password

    # Deploy the template to a resource group
    def deploy_resource_template(
        self, template_name: str, parameters: dict, compute=False, resource_group=None
    ) -> dict:
        """
        Deploy an Azure resource manager template from the 'arm_templates' directory.

        Args:
            template_name: The name of the template to deploy.
                The template must be in the 'arm_templates' directory and the name should not contain the extension.
            parameters: A dictionary of parameters

        Returns:
            The 'outputs' dictionary from the template.
        """
        if compute and resource_group:
            raise Exception("Cannot specify compute and resource_group kwargs.")
        elif compute:
            deploy_resource_group = self.compute_resource_group
        elif resource_group:
            deploy_resource_group = resource_group
        else:
            deploy_resource_group = self.resource_group

        # load arm template into json
        with open(
            "{}/{}.json".format(self.template_base_path, template_name), "r"
        ) as template_file_fd:
            template = json.load(template_file_fd)

        deployment_properties = {
            "mode": DeploymentMode.incremental,
            "template": template,
            "parameters": parameters,
        }

        deploy_uuid = str(uuid.uuid4())
        logger.info(
            f"Deploying {template_name} template to RG {deploy_resource_group} and region {self.location}"
            f" with deployment ID {deploy_uuid}."
        )
        try:
            deployment_async_operation = self.client.deployments.create_or_update(
                deploy_resource_group,
                "{}-{}".format(self.environment, deploy_uuid),
                deployment_properties,
            )
            result = deployment_async_operation.result()
        except CloudError as e:
            logger.error("Failed to deploy template {}.".format(template_name))
            logger.error(e.inner_exception.message)
            raise

        return result.properties.outputs

    def deploy_function(
        self, app_name: str, code_path: str, slot: str = None,
            resource_group: str = None
    ):
        """
        Deploy the given code folder to an Azure Function.

        Args:
            app_name: The name of the Function App to deploy to.
            code_path: The directory (relative to the script) that contains the code.
                This method assumes that the code has already been built and is in a 'build'
                folder under the specified directory.
                The 'build' directory will be zipped by this method.
            slot: The slot name suffix
            resource_group: The name of the resource group to deploy to.
        """
        logger.info("Begin function deployment process for {}.".format(app_name))

        if resource_group:
            resource_group = resource_group
        else:
            resource_group = self.compute_resource_group
        # zip up function directory
        if not os.path.isfile(code_path + "/build.zip"):
            self.zip_dir(Path(code_path,  "build"))

        # get publishing creds and slot URL to deploy function zip to App
        try:
            if slot:
                # If using a slot, we'll need the URL to publish to.
                slot_response = self.web_client.web_apps.get_slot(
                    resource_group, app_name, slot
                )
                auth_response = self.web_client.web_apps.list_publishing_credentials_slot(
                    resource_group, app_name, slot
                ).result()
            else:
                auth_response = self.web_client.web_apps.list_publishing_credentials(
                    resource_group, app_name
                ).result()
        except Exception as e:
            logger.error(
                "Failed to get publishing credentials for {}.".format(app_name)
            )
            self.thread_exceptions.append(e)
            raise e

        # publish zip deployment to App
        logger.info("Begin deploying zip file to {app}.".format(app=app_name))
        publishing_username = auth_response.publishing_user_name
        publishing_pw = auth_response.publishing_password

        if slot:
            url = (
                "https://"
                + slot_response.enabled_host_names[1]
                + "/api/zipdeploy?isAsync=true"
            )
            deployment_url = (
                "https://" + slot_response.enabled_host_names[1] + "/api/deployments"
            )
        else:
            url = "https://{app}.scm.azurewebsites.net/api/zipdeploy?isAsync=true".format(
                app=app_name
            )
            deployment_url = "https://{app}.scm.azurewebsites.net/api/deployments".format(
                app=app_name
            )

        with open(code_path.rstrip("/") + "/build.zip", "rb") as f:
            zip_file = f.read()

        for attemptNumber in range(10):
            zip_deploy_request = requests.post(
                url=url,
                headers={"Content-Type": "application/octet-stream"},
                data=zip_file,
                auth=HTTPBasicAuth(publishing_username, publishing_pw),
            )

            if zip_deploy_request.status_code in [200, 201, 202]:
                logger.info(
                    "Deployment submitted successfully for app {}.".format(app_name)
                )
                break
            elif attemptNumber < 9:
                logger.info(zip_deploy_request.text)
                logger.info(
                    f"Deployment submission unsuccessful for app {app_name} - retry {attemptNumber + 1}/10. Status {zip_deploy_request.status_code}"
                )
                time.sleep(25)
            else:
                logger.error(zip_deploy_request.text)
                deploy_function_exception = Exception(
                    "Function App code deployment failed for {}.".format(app_name)
                )
                self.thread_exceptions.append(deploy_function_exception)
                raise deploy_function_exception

        # Wait for deployment to complete
        counter = 0
        done = False
        error = None
        max_status_checks = 80
        while counter < max_status_checks and not done:
            deployment_request = requests.get(
                url=deployment_url,
                auth=HTTPBasicAuth(publishing_username, publishing_pw),
            )
            try:
                deployment = deployment_request.json()[0]
            except Exception as e:
                # Record exception and response to log if out of retries
                error = (e, deployment_request.text)
                deployment = {}
            if deployment.get("status") == 4 and deployment.get("complete"):
                logger.info("Deployment complete for app {}.".format(app_name))
                done = True
            elif deployment.get("status") == 3 and deployment.get("complete"):
                logger.error(deployment_request.text)
                deployment_exception = Exception(
                    f"Function deployment failed for {app_name}."
                )
                self.thread_exceptions.append(deployment_exception)
                raise deployment_exception
            else:
                counter += 1
                logger.info(
                    "Deployment not complete for app {} after {} check. Sleeping.".format(
                        app_name, counter
                    )
                )
                time.sleep(10)

        # If the counter got all the way up we timed out.
        if counter == max_status_checks and not done:
            if error is not None:
                e, text = error
                logger.error(text)
                logger.error(f'{type(e).__name__}: {str(e)}')
            timeout_exception = Exception(
                "Function deployment timed out for {}.".format(app_name)
            )
            self.thread_exceptions.append(timeout_exception)
            raise timeout_exception

        function_key = None
        # Swapping slot to production
        if slot:
            if "-fa-udp-" in app_name:
                # Adding function key to slot
                function_key = self.get_function_app_key(app_name)

                self.update_function_appsettings(
                    app_name, {"FunctionAppKey": function_key}, slot=slot
                )
            self.swap_slot(resource_group, app_name, slot)

        # Syncing the Function triggers.
        if "-fa-udp-" in app_name:
            self._sync_function_triggers(app_name, resource_group)
        return function_key

    def swap_slot(self, resource_group: str, app_name: str, slot: str):
        logger.info("Beginning API layer function-app swap")
        for swapAttemptCounter in range(1, 6):
            if swapAttemptCounter >= 5:
                logger.info(
                    "API layer function-app swap attempt {} failed. Final retry".format(
                        swapAttemptCounter
                    )
                )
                asyncCall = self.web_client.web_apps.swap_slot_with_production(
                    resource_group, app_name, slot, True
                )
                asyncCall.result()
                break
            try:
                asyncCall = self.web_client.web_apps.swap_slot_with_production(
                    resource_group, app_name, slot, True
                )
                asyncCall.result()
                logger.info("API layer function-app swap complete")
                break
            except Exception:
                logger.info(
                    "API layer function-app swap attempt {} failed. Retrying".format(
                        swapAttemptCounter
                    )
                )
                time.sleep(5)

    def update_function_appsettings(
        self, app_name: str, settings: dict, slot: str = None
    ):
        """
        Updates the application settings of a Function App.
        The method works by first getting the current application settings,
        then adding those in the argument dictionary.
        Existing settings are overwritten by those passed in the argument.

        Args:
            app_name: The Function App name to update.
            settings: The dictionary of settings to add/update.
        """
        if slot:
            app_settings = self.web_client.web_apps.list_application_settings_slot(
                self.compute_resource_group, app_name, slot
            )
        else:
            app_settings = self.web_client.web_apps.list_application_settings(
                self.compute_resource_group, app_name
            )
        new_settings = app_settings.properties
        new_settings.update(settings)

        if slot:
            self.web_client.web_apps.update_application_settings_slot(
                self.compute_resource_group,
                app_name,
                slot,
                kind="functionapp",
                properties=new_settings,
            )
        else:
            self.web_client.web_apps.update_application_settings(
                self.compute_resource_group,
                app_name,
                kind="functionapp",
                properties=new_settings,
            )

    def deploy_application_dashboard(self, application_resource_group: str):
        thread = threading.Thread(
            target=self._deploy_application_dashboard, args=[application_resource_group]
        )
        thread.start()
        self.app_dashboard_threads.append(thread)

    def _deploy_application_dashboard(self, application_resource_group: str):
        t = time.time()
        logger.info("Deploying application dashboard to main location")
        try:
            param_object = self.parameters_object.copy()
            param_object["location"] = {"value": self.location}
            param_object["regionCode"] = {"value": self.region_code}
            param_object["resourceGroup"] = {"value": application_resource_group}
            self.deploy_resource_template("applications_dashboard", param_object)

            # Redeploy in East US 2 for disaster recovery
            if self.dr_flag:
                logger.info("Deploying application dashboard to DR location")
                dr_param_object = param_object.copy()
                dr_param_object["location"] = {"value": self.dr_location}
                dr_param_object["regionCode"] = {"value": self.dr_region_code}
                self.deploy_resource_template("applications_dashboard", dr_param_object)

            logger.info(
                "Application dashboard deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )

        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def prep_event_hub_namespace(self, config_dict):
        """
        Preps and deploys necessary Event Hub Namesapces.
        This function will deploy as many Event Hub Namespaces as needed for the amount of sources,
        as only 10 event hubs can be under a single Event Hub Namespace.

        Args:
            config_dict: Dictionary with information from config file
        """
        existing_eh_namespaces = []
        existing_event_hubs = []
        existing_row_keys = []
        existing_eh_assignments = {}
        eh_sources_row_count = 0
        total_row_count = 0
        shared_source_namespace = None
        initial_deployment_flag = False

        all_rows = self.table_service.query_entities(
            self.source_table_name, filter="PartitionKey eq '{}'".format(self.app_name)
        )

        for row in all_rows:
            total_row_count += 1
            existing_row_keys.append(row.RowKey)
            if row.get("EventHub") and row.get("EventHubNamespace"):
                eh_sources_row_count += 1
                existing_event_hubs.append(row.EventHub)
                existing_eh_namespaces.append(row.EventHubNamespace)
                existing_eh_assignments.update(
                    {
                        row.EventHub: {
                            "EventHubNamespace": row.EventHubNamespace,
                            "RowKey": row.RowKey,
                        }
                    }
                )

        existing_eh_namespaces = sorted(list(set(existing_eh_namespaces)))

        if total_row_count == 0:
            initial_deployment_flag = True

        source_list = []
        event_hubs = []
        shared_sources_event_hubs = []
        consumer_groups = []

        if "sources" in config_dict.keys():
            # Only deploy source if active and we're deploying in default location
            # or config location matches current deployer location
            sources = [i for i in config_dict["sources"] if self.location in i.get("deployRegions", [defaults.LOCATION]) and i.get("enabled", True)]

            # Sources are already in the right format, so we don't need to modify them,
            # we just need to explode the DB tables.
            for source in sources:
                # TODO Move into ingestion classes
                if source["type"] == "db":
                    for table in source["properties"]["tables"]:
                        explode_source = {
                            "info": source["info"],
                            "type": source["type"],
                            "properties": source["properties"].copy(),
                        }
                        del explode_source["properties"]["tables"]
                        add_source = explode_source.copy()
                        add_source["eventHub"] = (
                            "source-db-"
                            + source["name"]
                            + "-"
                            + table["tableName"]
                            .lower()
                            .replace(" ", "_")
                            .replace("[", "")
                            .replace("]", "")
                            .replace(".", "")
                        )
                        add_source["name"] = (
                            "{}-{}".format(source["name"], table["tableName"])
                            .replace(" ", "_")
                            .replace("[", "")
                            .replace("]", "")
                            .replace(".", "")
                        )
                        add_source["properties"]["tableInfo"] = table
                        source_list.append(add_source)

                # TODO Move into ingestion classes
                elif source["type"] in ["batchfile", "udp", "api"] or source["type"] in ingestion_types:
                    if source["type"] == "api":
                        source["eventHub"] = f"source-{source['type']}-{source['name']}"
                    source_list.append(source)

        else:
            logger.info(
                "No sources section found in the config file!  Searching for Cosmos resources and API Endpoints..."
            )

        if config_dict.get("cosmosDatabaseAccounts"):
            logger.info("Found Cosmos resources! Adding to source count...")
            for database in config_dict["cosmosDatabaseAccounts"]["databases"]:
                # The Cosmos accounts look slightly different, so we conform them
                # to the source structure.
                for container in database["containers"]:
                    source_dict = {}
                    source_dict["name"] = (
                        self.app_name
                        + "-cosmos-"
                        + database["databaseName"]
                        + "-"
                        + container["containerName"]
                    )
                    source_dict["type"] = "cosmos"
                    source_dict["info"] = {
                        "description": container["description"],
                        "subjectArea": container["subjectArea"],
                        "region": container["region"],
                        "securityLevel": container["securityLevel"],
                    }
                    source_dict["properties"] = {
                        "databaseName": database["databaseName"],
                        "containerName": container["containerName"],
                        "key": container["key"],
                        "capture": container.get("capture", True),
                    }
                    source_dict["eventHub"] = "{}-cos-{}-{}".format(
                        self.app_name,
                        database["databaseName"],
                        container["containerName"],
                    )
                    source_list.append(source_dict)
        else:
            logger.info("No Cosmos Database Accounts found in the config file!")

        if config_dict.get("apiLayer"):
            logger.info("Found API Endpoints! Adding to source count...")
            for endpoint in config_dict["apiLayer"].get("endpoints", []):
                # Endpoints also have a different structure, so we conform those.
                source_dict = {}
                source_dict["name"] = f'{self.app_name}-endpoint-{endpoint["name"]}'
                source_dict["type"] = "endpoint"
                source_dict["endpointName"] = endpoint["name"]
                source_dict["properties"] = {"endpoint": endpoint["endpoint"]}
                snapshot = endpoint.get("snapshot", None)
                if snapshot is not None:
                    snapshot.update({"batch_file_type": "delta", "file_type": "ndjson"})
                    source_dict["properties"]["snapshot"] = snapshot
                source_dict["info"] = {
                    "description": endpoint["description"],
                    "subjectArea": endpoint["subjectArea"],
                    "securityLevel": endpoint["securityLevel"],
                    "region": endpoint["region"],
                }
                source_dict["eventHub"] = "{}-endpoint-{}".format(
                    self.app_name, endpoint["name"]
                )
                source_list.append(source_dict)
        else:
            logger.info("No API Endpoints found in the config file!")

        event_hub_namespaces = []
        filtered_sources_list = [
            item
            for item in source_list
            if item["type"] not in ["batchfile", "udp"]
            and item["type"] not in ingestion_types
        ]
        if not filtered_sources_list:
            logger.info("No Event Hub Namespaces to deploy!")
        else:
            if initial_deployment_flag:
                i = 0
                for n in range(0, len(filtered_sources_list), 10):
                    namespace_event_hubs = []
                    for item in filtered_sources_list[n : n + 10]:
                        # future consideration for consumption
                        # if item["sourceType"] == "":
                        #     item["eventHubNamespaceName"] = "{0}-{1}-eh-udp-{2}-cons-{3}-{4}".format(
                        #         self.org_name,
                        #         self.region_code,
                        #         self.app_name,
                        #         str(i),
                        #         self.environment
                        #     )
                        # else:
                        item[
                            "eventHubNamespaceName"
                        ] = "{0}-{1}-eh-udp-{2}-ing-{3}-{4}".format(
                            self.org_name,
                            self.region_code,
                            self.app_name,
                            str(i),
                            self.environment,
                        )
                        item["eventHubNamespaceIndex"] = i
                        event_hubs.append(
                            {
                                "namespace": item["eventHubNamespaceName"],
                                "event_hub": item["eventHub"],
                            }
                        )
                        consumer_groups.append(
                            {
                                "namespace": item["eventHubNamespaceName"],
                                "event_hub": item["eventHub"],
                                "consumer_group": "datalakeload",
                            }
                        )
                        namespace_event_hubs.append(item["eventHub"])
                    event_hub_namespaces.append(
                        {
                            "namespace": item["eventHubNamespaceName"],
                            "index": i,
                            "event_hubs": namespace_event_hubs,
                        }
                    )
                    i += 1
            else:
                for item in filtered_sources_list:
                    event_hubs.append({"event_hub": item["eventHub"]})

                table_entities_to_delete = []
                formatted_config_sources = []
                for source in source_list:
                    # TODO Will need to specify a subset of source types to add to list if certain source types are added to ingestion classes
                    formatted_config_sources.append(source["name"])

                for row in existing_row_keys:
                    if row not in formatted_config_sources:
                        table_entities_to_delete.append(row)

                eh_to_delete = []
                for row in all_rows:
                    if row.get("EventHub") and row.get("EventHubNamespace"):
                        if row.RowKey in table_entities_to_delete:
                            eh_to_delete.append(
                                {
                                    "EventHub": row.EventHub,
                                    "EventHubNamespace": row.EventHubNamespace,
                                }
                            )

                # Delete the event hubs that are no longer in config and need to be deleted
                for event_hub in eh_to_delete:
                    try:
                        self.eh_client.event_hubs.delete(
                            self.resource_group,
                            event_hub["EventHubNamespace"],
                            event_hub["EventHub"],
                        )
                    except ErrorResponseException as e:
                        if e.response.status_code == 404:
                            # EventHub no longer exists; no need to delete
                            pass
                        else:
                            raise

                # Delete table entities that are no longer in config and need to be deleted
                if table_entities_to_delete:
                    for entity in table_entities_to_delete:
                        existing_eh_assignments = {
                            k: v
                            for k, v in existing_eh_assignments.items()
                            if v["RowKey"] != entity
                        }
                        self.table_service.delete_entity(
                            self.source_table_name, self.app_name, entity
                        )

                # Delete unnecessary event hubs originally sourced from table
                event_hubs_list = [d["event_hub"] for d in event_hubs]
                for eh in existing_event_hubs[:]:
                    if eh not in event_hubs_list:
                        existing_event_hubs.remove(eh)

                new_event_hubs_to_deploy = []
                for d in event_hubs:
                    if d["event_hub"] not in existing_event_hubs:
                        new_event_hubs_to_deploy.append(d["event_hub"])

                new_assigned_event_hub_namespaces = {}
                for eh in existing_event_hubs:
                    if (
                        new_assigned_event_hub_namespaces == {}
                        or existing_eh_assignments[eh]["EventHubNamespace"]
                        not in new_assigned_event_hub_namespaces.keys()
                    ):
                        new_assigned_event_hub_namespaces[
                            existing_eh_assignments[eh]["EventHubNamespace"]
                        ] = [eh]
                    else:
                        new_assigned_event_hub_namespaces[
                            existing_eh_assignments[eh]["EventHubNamespace"]
                        ].append(eh)

                for key in new_assigned_event_hub_namespaces:
                    while (
                        len(new_assigned_event_hub_namespaces[key]) < 10
                        and new_event_hubs_to_deploy
                    ):
                        for eh in new_event_hubs_to_deploy[:]:
                            new_assigned_event_hub_namespaces[key].append(eh)
                            new_event_hubs_to_deploy.remove(eh)
                            break

                if new_event_hubs_to_deploy:
                    new_eh_raw_count = int(len(new_event_hubs_to_deploy) / 10)
                    new_eh_to_deploy = 0

                    if new_eh_raw_count < 1:
                        new_eh_to_deploy = 1
                    else:
                        if len(new_event_hubs_to_deploy) % 10 == 0:
                            new_eh_to_deploy = new_eh_raw_count
                        else:
                            new_eh_to_deploy += 1
                            new_eh_to_deploy += new_eh_raw_count

                    for i in range(new_eh_to_deploy):
                        d_length = len(new_assigned_event_hub_namespaces)
                        new_assigned_event_hub_namespaces[
                            "{0}-{1}-eh-udp-{2}-ing-{3}-{4}".format(
                                self.org_name,
                                self.region_code,
                                self.app_name,
                                str(d_length + i),
                                self.environment,
                            )
                        ] = []

                    for key in new_assigned_event_hub_namespaces:
                        while (
                            len(new_assigned_event_hub_namespaces[key]) < 10
                            and new_event_hubs_to_deploy
                        ):
                            for eh in new_event_hubs_to_deploy[:]:
                                new_assigned_event_hub_namespaces[key].append(eh)
                                new_event_hubs_to_deploy.remove(eh)
                                break

                for key in new_assigned_event_hub_namespaces:
                    for eh in event_hubs:
                        if eh["event_hub"] in new_assigned_event_hub_namespaces[key]:
                            eh.update({"namespace": key})

                for d in event_hubs:
                    consumer_groups.append(
                        {
                            "namespace": d["namespace"],
                            "event_hub": d["event_hub"],
                            "consumer_group": "datalakeload",
                        }
                    )

                for k in new_assigned_event_hub_namespaces:
                    event_hub_namespaces.append(
                        {
                            "namespace": k,
                            "index": [int(s) for s in k.split("-") if s.isdigit()][0],
                            "event_hubs": new_assigned_event_hub_namespaces[k],
                        }
                    )

        # Add back batchfile and shared sources in filtered source list for insertion into sources table
        for s in source_list:
            if s["type"] in ["batchfile", "udp"]:
                filtered_sources_list.append(s)

        # Add the eventHubNamespaceName to the source
        for item in filtered_sources_list:
            if (
                item["type"] not in ["batchfile", "udp"]
                and item["type"] not in ingestion_types
            ):
                for d in event_hub_namespaces:
                    if item["eventHub"] in d["event_hubs"]:
                        item["eventHubNamespaceName"] = d["namespace"]
                        item["eventHubNamespaceIndex"] = d["index"]

        # Removing the Cosmos capture zip if it exists.
        if os.path.exists(
            "{}/cosmos_capture/build.zip".format(self.shared_functions_base_path)
        ):
            os.remove(
                "{}/cosmos_capture/build.zip".format(self.shared_functions_base_path)
            )

        # Insert source records into UDP Sources table
        for source in filtered_sources_list:
            if source["type"] not in ingestion_types:
                # TODO Move to ingestion classes
                if source["type"] == "db":
                    logger.info(
                        "Inserting {} source into source table.".format(source["name"])
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": source["info"]["description"],
                        "Region": source["info"]["region"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "Type": source["type"],
                        "DBServer": source["properties"]["dbServer"],
                        "DBName": source["properties"]["dbName"],
                        "DBType": source["properties"]["dbType"],
                        "Schedule": source["properties"]["tableInfo"][
                            "refreshSchedule"
                        ],
                        "DBTable": source["properties"]["tableInfo"]["tableName"],
                        "EventHubNamespace": source["eventHubNamespaceName"],
                        "EventHub": source["eventHub"],
                        "EventHubResourceGroup": self.resource_group,
                    }
                    if source["info"].get("sourceSystem"):
                        source_table_entity["SourceSystem"] = source["info"]["sourceSystem"]

                # TODO Move to ingestion classes
                elif source["type"] == "api":
                    logger.info(
                        "Inserting {} source into source table.".format(source["name"])
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": source["info"]["description"],
                        "Region": source["info"]["region"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "Type": source["type"],
                        "SourceURL": source["properties"]["source_url"],
                        "Schedule": source["properties"]["schedule"],
                        "EventHubNamespace": source["eventHubNamespaceName"],
                        "EventHub": source["eventHub"],
                        "EventHubResourceGroup": self.resource_group,
                    }
                    if source["info"].get("sourceSystem"):
                        source_table_entity["SourceSystem"] = source["info"]["sourceSystem"]

                elif source["type"] == "batchfile":
                    logger.info(
                        "Inserting {} source into source table.".format(source["name"])
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": source["info"]["description"],
                        "Region": source["info"]["region"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "Type": "batchfile",
                    }
                    if source["info"].get("sourceSystem"):
                        source_table_entity["SourceSystem"] = source["info"]["sourceSystem"]

                elif source["type"] == "cosmos":
                    if not source["properties"]["capture"]:
                        continue
                    logger.info(
                        "Inserting Cosmos capture source for {}/{} into source table.".format(
                            source["properties"]["databaseName"],
                            source["properties"]["containerName"],
                        )
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": source["info"]["description"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "Region": source["info"]["region"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "Type": source["type"],
                        "EventHubNamespace": source["eventHubNamespaceName"],
                        "EventHub": source["eventHub"],
                        "EventHubResourceGroup": self.resource_group,
                        "SourceSystem": "udp"
                    }

                    # TODO: This might not be the best place for the Cosmos capture code, but it's the easiest.
                    # Setting up the Cosmos capture function.
                    cc_path = "{}/cosmos_capture/build/{}".format(
                        self.shared_functions_base_path,
                        "{}-{}".format(
                            source["properties"]["databaseName"],
                            source["properties"]["containerName"],
                        ),
                    )
                    if not os.path.exists(cc_path):
                        os.mkdir(cc_path)
                    cc_json_path = "{}/function.json".format(cc_path)
                    with open(cc_json_path, "w") as f:
                        bindings = [
                            {
                                "type": "cosmosDBTrigger",
                                "databaseName": source["properties"]["databaseName"],
                                "collectionName": source["properties"]["containerName"],
                                "connectionStringSetting": "CosmosDBConnectionString",
                                "leaseCollectionName": "udp-leases",
                                "createLeaseCollectionIfNotExists": True,
                                "direction": "in",
                                "name": "input",
                            },
                            {
                                "type": "eventHub",
                                "name": "outputEvents",
                                "eventHubName": source["eventHub"],
                                "connection": "EventHub{}Connection".format(
                                    source["eventHubNamespaceIndex"]
                                ),
                                "direction": "out",
                            },
                        ]
                        func_json = json.dumps(
                            {
                                "bindings": bindings,
                                "disabled": False,
                                "scriptFile": "../bin/cosmos_capture.dll",
                                "entryPoint": "Cosmos.Capture.Run",
                            }
                        )
                        f.write(func_json)

                elif source["type"] == "endpoint":
                    logger.info(
                        "Inserting endpoint source for {} into source table.".format(
                            source["endpointName"]
                        )
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Type": source["type"],
                        "Description": source["info"]["description"],
                        "Region": source["info"]["region"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "EventHubNamespace": source["eventHubNamespaceName"],
                        "EventHub": source["eventHub"],
                        "EventHubResourceGroup": self.resource_group,
                    }
                    if source["info"].get("sourceSystem"):
                        source_table_entity["SourceSystem"] = source["info"]["sourceSystem"]

                elif source["type"] == "udp":
                    logger.info(
                        "Found shared UDP source. Checking sources table for info."
                    )
                    try:
                        source_entry = self.table_service.get_entity(
                            self.source_table_name,
                            source["properties"]["appName"],
                            source["properties"]["sourceName"],
                        )
                        source_resource_group = source_entry.EventHubResourceGroup
                        source_namespace = source_entry.EventHubNamespace
                        source_event_hub = source_entry.EventHub

                        if source_entry.Type not in ["api", "db", "cosmos", "endpoint"]:
                            # Currently only Event Hub sources are supported.
                            # Batchfiles, the third source type, need further enhancement
                            # to be subscribed to.
                            raise Exception(
                                "Requested app source is of type {}, which is not allowed as a shared source.".format(
                                    source.Type
                                )
                            )

                        if source_entry.SecurityLevel == "confidential":
                            # Confidential and restricted sources are not available.
                            # These will need some sort of permissioning/approval mechanism
                            # in order to work securely.
                            raise Exception(
                                "Request app source has a confidential security level, and cannot be shared."
                            )

                    except AzureMissingResourceHttpError as e:
                        logger.warning(
                            "Could not find the specified UDP source {} from application {}. This could be because you are deploying in a testing environment, or because the specified source/application combination does not exist. If you are in a testing environment there's nothing to worry about. An Event Hub is being created in your application's shered sources event ingestion namespace for testing.".format(
                                source["properties"]["sourceName"],
                                source["properties"]["appName"],
                            )
                        )
                        source_resource_group = self.resource_group
                        source_namespace = "{0}-{1}-eh-udp-{2}-ing-shared-{3}".format(
                            self.org_name,
                            self.region_code,
                            self.app_name,
                            self.environment
                        )
                        shared_source_namespace = source_namespace
                        namespace_parameters = EHNamespace(
                            location=self.location,
                            tags={
                                "AppName": self.parameters_object["projectInformation"]["value"]["AppName"],
                                "AppOwner": self.parameters_object["projectInformation"]["value"]["AppOwner"],
                                "BusLine": self.parameters_object["projectInformation"]["value"]["BusLine"],
                                "CostCenter": self.parameters_object["projectInformation"]["value"]["CostCenter"],
                                "Environment": self.parameters_object["projectInformation"]["value"]["Environment"],
                                "TechOwner": self.parameters_object["projectInformation"]["value"]["TechOwner"],
                                "OwnerEmail": self.parameters_object["projectInformation"]["value"]["OwnerEmail"],
                                "Description": "An ingestion Event Hub namespace. This namespace contains Event Hubs for all of the shared sources.",
                                "LastDeployedUTC": dt.utcnow()
                            },
                            sku=Sku(name=config_dict["eventHubNamespace"]["eventhubSku"], tier=config_dict["eventHubNamespace"]["eventhubSku"], capacity=config_dict["eventHubNamespace"]["skuCapacity"]),
                            is_auto_inflate_enabled=True,
                            maximum_throughput_units=10
                        )
                        logger.info("Creating an Event Hub Ingestion Namespace for shared sources.")
                        poller = self.eh_client.namespaces.create_or_update(
                            source_resource_group,
                            source_namespace,
                            parameters=namespace_parameters,
                            polling=True
                        )
                        poller.result()
                        source_event_hub = "shared-{}".format(
                            source["properties"]["sourceName"]
                        )
                        self.eh_client.event_hubs.create_or_update(
                            source_resource_group,
                            source_namespace,
                            source_event_hub,
                            Eventhub(message_retention_in_days=1, partition_count=8),
                        )
                        shared_sources_event_hubs.append(source_event_hub)


                    logger.info("Getting or creating auth rule for shared source.")
                    # Keys are created at the Event Hub level. This prevents a key with permissions
                    # to access a potential restricted dataset.
                    auth_rule = self.eh_client.event_hubs.create_or_update_authorization_rule(
                        source_resource_group,
                        source_namespace,
                        source_event_hub,
                        "shared-{}".format(self.app_name),
                        rights=["listen"],
                    )

                    logger.info(
                        "Inserting shared UDP source {} into source table.".format(
                            source["name"]
                        )
                    )
                    source_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": "This is a shared source from another application.",
                        "Type": "shared",
                        "EventHubNamespace": source_namespace,
                        "EventHub": source_event_hub,
                        "EventHubResourceGroup": source_resource_group,
                        "EventHubAuthRule": "shared-{}".format(self.app_name),
                        "SharedApp": source["properties"]["appName"],
                        "SharedSource": source["properties"]["sourceName"],
                        "SourceSystem": "udp"
                    }

                # Check if the source name is already in use by another application.
                # If it is, fail the deployment.
                source_name = source_table_entity["RowKey"]
                source_entries = list(
                    self.table_service.query_entities(
                        self.source_table_name,
                        filter=f"RowKey eq '{source_name}' and PartitionKey ne '{self.app_name}'",
                        select="PartitionKey, RowKey",
                    )
                )

                if len(source_entries) > 0:
                    in_use_app = source_entries[0].PartitionKey
                    logger.error(
                        f"Source {source_name} already exists in application {in_use_app}."
                    )
                    raise SourceNameInUse(
                        "Source names must be unique across applications."
                    )

                self.table_service.insert_or_replace_entity(
                    self.source_table_name, source_table_entity
                )

        self.event_hub_namespaces = event_hub_namespaces
        self.event_hubs = event_hubs
        self.consumer_groups = consumer_groups
        self.source_list = source_list
        self.shared_sources_event_hub_namespace = shared_source_namespace
        self.shared_sources_event_hubs = shared_sources_event_hubs

    def clean_event_hubs(self):
        # Get current namespaces and Event Hubs.
        namespaces = self.eh_client.namespaces.list_by_resource_group(
            self.resource_group
        )
        regex = re.compile(f"-{self.app_name}-.*{self.environment}$")
        app_namespaces = list(filter(lambda n: regex.search(n.name), namespaces))
        if self.event_hub_namespaces:
            event_hub_namespaces = self.event_hub_namespaces[:]
        else:
            event_hub_namespaces = list()
        if self.shared_sources_event_hub_namespace:
            event_hub_namespaces.append(
                {
                    "namespace": self.shared_sources_event_hub_namespace,
                    "event_hubs": self.shared_sources_event_hubs
                }
            )
        for namespace in app_namespaces:
            try:
                # Check the existing event hubs and delete any orphaned ones.
                deploy_hubs = list(
                    filter(
                        lambda n: namespace.name == n["namespace"],
                        event_hub_namespaces
                    )
                )[0]["event_hubs"]

                existing_hubs = self.eh_client.event_hubs.list_by_namespace(
                    self.resource_group, namespace.name
                )

                # Check if each existing hub is in the deployment. If not, delete it.
                for hub in existing_hubs:
                    if hub.name not in deploy_hubs:
                        logger.info(
                            f"Deleting unused Event Hub {hub.name} in namespace {namespace.name}"
                        )
                        self.eh_client.event_hubs.delete(
                            self.resource_group, namespace.name, hub.name
                        )

            except IndexError:
                # If there are no event hubs to deploy, delete the namespace.
                logger.info(f"Deleting unused namespace {namespace.name}.")
                self.eh_client.namespaces.delete(self.resource_group, namespace.name)

    def create_app_lake_folder(self):
        logger.info(
            "Creating application filesystems and folder and setting up ACLs in lake."
        )
        adls_client = DataLakeGen2Client(self.lake_account_name, self.lake_account_key)
        app_filesystem = "app"
        adls_client.create_filesystem(app_filesystem)
        adls_client.create_path(app_filesystem, f"/{self.app_name}/")

        # Set ACL at root path
        root_acl = [
            f"default:group:{self.core_role_group}:r-x",
            f"group:{self.core_role_group}:r-x",
            f"group:{self.app_ad_group_id}:r-x",
        ]

        adls_client.set_path_acl(app_filesystem, "/", add_acl=root_acl)

        # Set ACL at app path.
        path_acl = [
            f"default:group:{self.core_role_group}:r-x",
            f"group:{self.core_role_group}:r-x",
            f"default:group:{self.app_ad_group_id}:r-x",
            f"group:{self.app_ad_group_id}:r-x",
        ]
        # Need to dedupe incase the groups are the same.
        seen = {}
        dedupe_path_acl = []
        for item in path_acl:
            if item in seen:
                continue
            seen[item] = 1
            dedupe_path_acl.append(item)
        adls_client.set_path_acl(
            app_filesystem, f"/{self.app_name}/", new_acl=",".join(dedupe_path_acl)
        )

    def deploy_main_app_template(
        self,
        additional_parameters: dict,
        sku: str,
        sku_capacity: str,
        cost_center: str,
        owned_by: str,
    ):
        """
        Deploy the main application template to Azure.
        This template contains most of the required resources for an application,
        including monitoring, dashboarding, etc.

        Args:
            additional_parameters: Any additional parameters to add to the param object for deployment.
            sku: The SKU to deploy.
            sku_capacity: The capacity of Event Hub to deploy.
            cost_center: The cost center to which the Event Hub should be tied.
            owned_by: The owner of the Event Hub.
            namespace_name: The predetermined name for the Event Hub Namespace to ensure Event Hub limit is not exceeded
        """
        t = time.time()
        self.get_subdir_sizes(self.shared_functions_base_path + "/batchfile_ingestion/build/")
        logger.info("Deploying main template for app {}.".format(self.app_name))
        param_object = self.parameters_object.copy()
        param_object["eventhubNamespaces"] = {
            "value": [x["namespace"] for x in self.event_hub_namespaces]
        }
        param_object["eventHubs"] = {"value": self.event_hubs}
        param_object["consumerGroups"] = {"value": self.consumer_groups}
        param_object["eventhubSku"] = {"value": sku}
        param_object["skuCapacity"] = {"value": str(sku_capacity)}
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["dlResourceGroup"] = {"value": self.udp_resource_group}
        param_object["webResourceGroup"] = {"value": self.web_resource_group}
        param_object["appAdGroupId"] = {"value": self.app_ad_group_id}
        param_object["networking"] = {"value": defaults.pe_vnet_injection_map}
        param_object.update(additional_parameters)
        if self.email_receivers:
            param_object["emailReceivers"] = {"value": self.email_receivers}
        if self.app_object_id:
            param_object["appObjectId"] = {"value": self.app_object_id}

        logger.info("Deploying Event Hub namespace to main location")
        outputs = self.deploy_resource_template("app_main", param_object)

        # Grabbing the keys for each namespace and adding them to the dict.
        for namespace in self.event_hub_namespaces:
            rule_keys = self.eh_client.namespaces.list_keys(
                self.resource_group, namespace["namespace"], "listen-key"
            )
            namespace["listen_key"] = rule_keys.primary_connection_string
            rule_keys = self.eh_client.namespaces.list_keys(
                self.resource_group, namespace["namespace"], "send-key"
            )
            namespace["send_key"] = rule_keys.primary_connection_string

        self.log_workspace_name = outputs["workspaceName"]["value"]
        self.azure_key_vault = outputs["azureKeyvaultName"]["value"]
        self.search_name = outputs["azureSearchName"]["value"]
        self.signalr_connection_string = outputs["signalRConnectionString"]["value"]
        self.real_time_server = outputs["sqlServerName"]["value"]
        if additional_parameters.get("sqlDatabases"):
            self.sql_databases = additional_parameters["sqlDatabases"]["value"]
        self.real_time_user = additional_parameters.get(
            "sqlAdministratorLogin", {}
        ).get("value")
        self.real_time_password = additional_parameters.get(
            "sqlAdministratorLoginPassword", {}
        ).get("value")
        self.real_time_cosmos_connection = outputs["cosmosDBConnectionString"]["value"]
        self.utils_app_name = outputs["functionAppName"]["value"]
        self.app_storage_name = outputs["appStorageName"]["value"]
        self.app_storage_key = outputs["appStorageKey"]["value"]
        self.cosmos_url = outputs["cosmosDBURL"]["value"]
        self.cosmos_key = outputs["cosmosDBKey"]["value"]
        self.cosmos_key_read_only = outputs["cosmosDBKeyReadOnly"]["value"]

        # Dummy strings for all secrets.
        # This is to prevent resources from failing to find a secret during deployment.
        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "batchfile-queue-storage-connection",
            "default",
        )

        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "api-ingestion-queue-conn",
            "default",
        )

        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "db-ingestion-queue-conn",
            "default",
        )

        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "cons-event-hub-send-conn",
            "default",
        )

        # self.kv_client.set_secret(
        #        "https://{key_vault_name}.vault.azure.net".format(key_vault_name=self.azure_key_vault), "cosmos-url", "default")

        # self.kv_client.set_secret(
        #        "https://{key_vault_name}.vault.azure.net".format(key_vault_name=self.azure_key_vault), "cosmos-key", "default")

        # Redeploy in East US 2 for disaster recovery
        if self.dr_flag:
            logger.info("Deploying Event hub namespace to DR location")
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}
            output_dr = self.deploy_resource_template("app_main", dr_param_object)

            logger.info(
                "Vaulting Event hub namespace connections to {} key vault".format(
                    self.azure_key_vault_dr
                )
            )

        logger.info(
            "Event Hub namespace deployment finished successfully after {}.".format(
                timedelta(seconds=(time.time() - t))
            )
        )

        logger.info("Creating table UDPAPPS")
        param_object = self.parameters_object.copy()

        source_apps_table_entity = {
            "PartitionKey": "udp",
            "RowKey": self.app_name,
            "OrgName": self.org_name,
            "AppOwner": param_object["projectInformation"]["value"]["AppOwner"],
            "BusLine": param_object["projectInformation"]["value"]["BusLine"],
            "CostCenter": param_object["projectInformation"]["value"]["CostCenter"],
            "TechOwner": param_object["projectInformation"]["value"]["TechOwner"],
            "OwnerEmail": param_object["projectInformation"]["value"]["OwnerEmail"],
            "AppADGroupID": self.app_ad_group_id,
        }

        logger.info(f"Setting up Storage Analytics logging on the {self.app_storage_name} storage account.")

        # Creating the blob service client with the name and key. These were captured as
        # output of the application main ARM template.
        blob_service_client = BlobServiceClient(account_url=f"https://{self.app_storage_name}.blob.core.windows.net", credential=self.app_storage_key)
        # Create logging settings
        logging = BlobAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        # Create metrics for requests statistics
        hour_minute_metrics = Metrics(enabled=True, include_apis=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        blob_service_client.set_service_properties(analytics_logging=logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        # Set Storage Analytics Properties for Queues
        queue_service_client = QueueServiceClient(account_url=f"https://{self.app_storage_name}.queue.core.windows.net/", credential=self.app_storage_key)
        queue_logging = QueueAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        queue_service_client.set_service_properties(analytics_logging=queue_logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        # Set Storage Analytics Properties for Tables
        table_logging = Logging(delete=True, read=True, write=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        self.table_service.set_table_service_properties(logging=table_logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        self.table_service.create_table(self.apps_table_name)

        self.table_service.insert_or_replace_entity(
            self.apps_table_name, source_apps_table_entity
        )

    def deploy_consumption_event_hub_namespace(
        self, sku: str, sku_capacity: str, cost_center: str, owned_by: str
    ):
        thread = threading.Thread(
            target=self._deploy_consumption_event_hub_namespace,
            args=(sku, sku_capacity, cost_center, owned_by),
        )
        thread.start()
        self.namespace_threads.append(thread)

    def _deploy_consumption_event_hub_namespace(
        self, sku: str, sku_capacity: str, cost_center: str, owned_by: str
    ):
        """
        Deploy an Event Hub namespace to Azure.

        Args:
            sku: The SKU to deploy.
            sku_capacity: The capacity of Event Hub to deploy.
            cost_center: The cost center to which the Event Hub should be tied.
            owned_by: The owner of the Event Hub.
        """
        t = time.time()
        try:
            logger.info(
                "Deploying Consumption Event Hub namespace for app {}.".format(
                    self.app_name
                )
            )
            param_object = self.parameters_object.copy()
            param_object["eventhubSku"] = {"value": sku}
            param_object["skuCapacity"] = {"value": str(sku_capacity)}
            param_object["costCenter"] = {"value": cost_center}
            param_object["ownedBy"] = {"value": owned_by}
            param_object["location"] = {"value": self.location}
            param_object["regionCode"] = {"value": self.region_code}
            param_object["workspaceName"] = {"value": self.log_workspace_name}
            param_object["environment"] = {"value": self.compute_environment}

            logger.info("Deploying Consumption Event Hub namespace to main location")
            outputs = self.deploy_resource_template(
                "consumption_event_hub_namespace", param_object, compute=True
            )

            self.cons_event_hub_send_conn = outputs[
                "sendConnectionStringConsumptionNamespace"
            ]["value"]

            logger.info(
                "Vaulting Consumption Event Hub namespace connection to {} key vault".format(
                    self.azure_key_vault
                )
            )
            self.kv_client.set_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault
                ),
                "cons-event-hub-send-conn",
                outputs["sendConnectionStringConsumptionNamespace"]["value"],
            )

            # Redeploy in East US 2 for disaster recovery
            if self.dr_flag:
                logger.info("Deploying Consumption Event hub namespace to DR location")
                dr_param_object = param_object.copy()
                dr_param_object["location"] = {"value": self.dr_location}
                dr_param_object["regionCode"] = {"value": self.dr_region_code}
                output_dr = self.deploy_resource_template(
                    "consumption_event_hub_namespace", dr_param_object, compute=True
                )
                self.cons_event_hub_send_conn_dr = output_dr[
                    "sendConnectionStringConsumptionNamespace"
                ]["value"]
                logger.info(
                    "Vaulting Consumption Event Hub namespace connection to {} key vault".format(
                        self.azure_key_vault_dr
                    )
                )
                self.kv_client.set_secret(
                    "https://{key_vault_name}.vault.azure.net".format(
                        key_vault_name=self.azure_key_vault_dr
                    ),
                    "cons-event-hub-send-conn",
                    output_dr["sendConnectionStringConsumptionNamespace"]["value"],
                )
            logger.info(
                "Consumption Event Hub namespace deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def _sync_function_triggers(
            self, function_app_name: str, resource_group: str
    ):
        max_attempts: int = 10
        for attemptNum in range(1, max_attempts + 1):
            logger.info(
                f"Attempt {attemptNum}/{max_attempts} to sync "
                f"{function_app_name} function triggers beginning"
            )
            try:
                _ = self.web_client.web_apps.sync_function_triggers(
                    resource_group, function_app_name
                )
                break
            except Exception as e:
                response = getattr(e, 'response', None)
                status_code = getattr(e, 'status_code', None)
                if status_code is None and response is not None:
                    status_code = getattr(response, 'status_code', None)
                if status_code == 200:
                    break
                elif attemptNum < max_attempts:
                    logger.warning(
                        f"Attempt {attemptNum}/{max_attempts} to sync "
                        f"{function_app_name} function triggers failed"
                    )
                else:
                    logger.error(e)
                    if response is not None:
                        logger.error(e.response.text)
                    self.thread_exceptions.append(e)
                    return
            time.sleep(5)
        logger.info(
            f"Successfully synced {function_app_name} function triggers"
        )

    def _deploy_function_to_blob(
            self, function_app_name: str, code_path: typing.Union[Path, str]
    ) -> str:
        """
        Deploy zipped function code to Azure Blob storage and return the SAS URL.
        """
        logger.info("Pushing zip file to app storage.")

        build_path = Path(code_path, "build")
        self.get_subdir_sizes(build_path)
        zip_path = Path(code_path, "build.zip")
        if not zip_path.exists():
            self.zip_dir(build_path)
        zip_size = os.path.getsize(zip_path)
        logger.info(f"Size of zip file {zip_path} is {zip_size}.")

        # Creating the blob service with the name and key. These were captured
        # as output of the application main ARM template.
        account_url = f"https://{self.app_storage_name}.blob.core.windows.net"
        blob_service_client = BlobServiceClient(
            account_url=account_url, credential=self.app_storage_key
        )

        # Creating the storage container for this and any function code,
        # if it doesn't exist.
        container_name = 'function-code'
        try:
            blob_service_client.create_container(container_name)
        except ResourceExistsError:
            logger.info(f"Container {container_name} already exists!")
        except Exception as e:
            logger.error(e)
            self.thread_exceptions.append(e)

        # Publishing the zip file to the container. We prefix the blob
        # with an identifier for the zip, as well as a random ID.
        # TODO: Might want to put timestamps in the names so they sort
        # better.
        # TODO: Definitely need to start trimming these at some point,
        # instead of leaving them out there forever.
        deployment_file = f"{function_app_name}-{str(uuid.uuid4())}.zip"
        blob_client = blob_service_client.get_blob_client(
            container=container_name, blob=deployment_file
        )
        with open(zip_path, "rb") as data:
            blob_client.upload_blob(data=data, overwrite=True)

        # Creating a SAS token for the app to read the blob.
        code_sas = generate_blob_sas(
            account_name=self.app_storage_name,
            container_name=container_name,
            blob_name=deployment_file,
            account_key=self.app_storage_key,
            permission=BlobSasPermissions(read=True),
            expiry=add_years(dt.utcnow(), 10)
        )

        code_sas_url = (
            f"{account_url}/{container_name}/{deployment_file}?{code_sas}"
        )
        return code_sas_url

    def deploy_function_app(
        self,
        tag: str,
        code_path: str,
        description: str,
        event_hub_name: str = "",
        runtime: str = None,
        hostingPlan: str = None,
        networking: dict = None,
        cosmos_db_name: str = None,
        cosmos_db_collection: str = None,
        source_info: dict = None,
        source_name: str = None,
        app_settings: dict = None,
        singleAspFlag: bool = False,
        use_blob: bool = False,
    ):
        """
        Deploy an Azure Function App complete with code.

        Args:
            tag: A tag to add to the name of the Function App.
            code_path: The directory (relative to the script) that contains the code.
                This method assumes that the code has already been built and is in a 'build'
                folder under the specified directory.
                The 'build' directory will be zipped by this method.
            event_hub_name (optional): The name of the Event Hub to add to the AppSettings.
            hostingPlan : The type of hosting plan to deploy for a function app.
        """
        logger.info(
            "Deploying Function App with tag {} for app {} in Hosting plan {}.".format(
                tag, self.app_name, hostingPlan
            )
        )
        param_object = self.parameters_object.copy()
        param_object["tag"] = {"value": tag}
        if source_name:
            param_object["sourceName"] = {"value": source_name}
        else:
            param_object["sourceName"] = {"value": tag}
        param_object["eventHubName"] = {"value": event_hub_name}
        param_object["storageAccountName"] = {"value": self.lake_account_name}
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["keyVaultName"] = {"value": self.azure_key_vault}
        param_object["description"] = {"value": description}
        param_object["udpResourceGroup"] = {"value": self.udp_resource_group}
        param_object["appResourceGroup"] = {"value": self.resource_group}
        if runtime:
            param_object["runtime"] = {"value": runtime}
        if self.search_name:
            param_object["azureSearchName"] = {"value": self.search_name}
        if cosmos_db_name:
            param_object["cosmosDBName"] = {"value": cosmos_db_name}
        if cosmos_db_collection:
            param_object["cosmosDBCollection"] = {"value": cosmos_db_collection}
        if self.cosmos_url:
            param_object["cosmosDBUrl"] = {"value": self.cosmos_url}
        if self.cosmos_key:
            param_object["cosmosKey"] = {"value": self.cosmos_key}
        if source_info:
            param_object["sourceDescription"] = {"value": source_info["description"]}
            param_object["sourceRegion"] = {"value": source_info["region"]}
            param_object["sourceSecurityLevel"] = {
                "value": source_info["securityLevel"]
            }
            param_object["sourceSubjectArea"] = {"value": source_info["subjectArea"]}
        if self.sql_flag:
            param_object["sqlAdministratorLogin"] = {"value": self.real_time_user}
            param_object["sqlAdministratorLoginPassword"] = {
                "value": self.real_time_password
            }
        if self.databricks_token:
            param_object["databricksToken"] = {"value": self.databricks_token}

        param_object["searchFlag"] = {"value": self.search_flag}
        param_object["signalRFlag"] = {"value": self.signalr_flag}
        param_object["sqlFlag"] = {"value": self.sql_flag}
        param_object["cosmosFlag"] = {"value": self.cosmos_flag}

        # Because function_app.json uses a nested template, we need to escape
        # by prepending "[" or Azure will attempt to evaluate it as an ARM
        # expression rather than a string
        param_object["emailReceivers"] = {
            "value": "[" + json.dumps(self.email_receivers)
        }

        if app_settings:
            param_object["appSettings"] = {
                "value": [{"name": k, "value": v} for k, v in app_settings.items()]
            }

        if hostingPlan:
            param_object["hostingPlan"] = {"value": hostingPlan}

        param_object["singleAspFlag"] = {"value": singleAspFlag}

        if networking:
            if networking["vnet"]:
                logger.info("Deploying Realtime layer with VNet Connection VNet = "+ networking["vnet"]["vnetName"] +" and Subnet = "+networking["vnet"]["subnetName"] )
                param_object["vnetConnection"] = {"value": networking["vnet"]}

        # Python runtimes require Linux Function apps, which are deployed as ASPs
        # under the Web RG due to an Azure limitation
        if runtime == "python":
            deploy_resource_group = self.web_resource_group
        else:
            deploy_resource_group = self.compute_resource_group

        logger.info("Deploying function app to main location")
        if use_blob:
            # Deploy code as zip to Azure blob
            code_sas_url = self._deploy_function_to_blob(tag, code_path)
            param_object["codeSas"] = {"value": code_sas_url}

            # Deploy ARM template
            outputs = self.deploy_resource_template(
                "function_app", param_object,
                resource_group=deploy_resource_group
            )
            logger.info("Deployment successful")
            function_app_name = outputs["functionAppName"]["value"]

            # Sync Function triggers
            self._sync_function_triggers(
                function_app_name, deploy_resource_group
            )
        else:
            # Deploy ARM template
            outputs = self.deploy_resource_template(
                "function_app", param_object,
                resource_group=deploy_resource_group
            )
            logger.info("Deployment successful")

            # Deploy code as ZIP file package
            logger.info("Deploy function app code in main location")
            function_app_name = outputs["functionAppName"]["value"]
            self.deploy_function(
                function_app_name, code_path,
                resource_group=deploy_resource_group
            )
            logger.info("Deployment successful")

        if self.dr_flag:
            # Redeploy in East US 2 for disaster recovery
            logger.info("Deploying function app to DR location")
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}

            # Deploy ARM template
            output_dr = self.deploy_resource_template(
                "function_app", dr_param_object,
                resource_group=deploy_resource_group
            )
            logger.info("Deployment successful")
            function_app_name_dr = output_dr["functionAppName"]["value"]

            if use_blob:
                # Code ZIP already deployed to Azure blob, just need to sync
                # function triggers
                self._sync_function_triggers(
                    function_app_name_dr, deploy_resource_group
                )
            else:
                # Deploy code as ZIP file package
                logger.info("Deploying function app code in DR location")
                self.deploy_function(
                    function_app_name_dr, code_path,
                    resource_group=deploy_resource_group
                )
                logger.info("Deployment successful")

        return function_app_name

    def deploy_consumer_group(
        self,
        event_hub_name: str,
        consumer_group_name: str,
        resource_group=None,
        namespace=None,
    ):
        """
        Deploy a consumer group to an Azure Event Hub.

        Args:
            event_hub_name: The name of the Event Hub to deploy to.
            consumer_group_name: The name of the consumer group to deploy.
            namepsace (optional): A namespace to deploy to. Defaults to the ingestion namespace.
        """
        if not namespace:
            namespace = self.event_hub_namespace

        if not resource_group:
            resource_group = self.compute_resource_group

        logger.info("Deploying consumer group for Event Hub {}.".format(event_hub_name))
        self.eh_client.consumer_groups.create_or_update(
            resource_group, namespace, event_hub_name, consumer_group_name
        )

        logger.info(
            "Consumer group {} deployment successful.".format(consumer_group_name)
        )

    def deploy_api_layer(
        self,
        endpoints: list,
        runtime: str,
        type: str,
        custom_secrets=None,
        asp_autoscale_settings=None,
        sku=None,
        hosting_plan=None
    ):
        self.wait_sources()
        self.wait_batch()
        thread = threading.Thread(
            target=self._deploy_api_layer,
            args=(
                endpoints,
                runtime,
                type,
                custom_secrets,
                asp_autoscale_settings,
                sku,
                hosting_plan,
            ),
        )
        thread.start()
        self.api_threads.append(thread)

    def _deploy_api_layer(
        self,
        endpoints: list,
        runtime: str,
        type: str,
        custom_secrets=None,
        asp_autoscale_settings=None,
        sku=None,
        hosting_plan=None
    ):
        """
        Deploy the API layer for an application.

        """
        t = time.time()
        try:
            logger.info("Deploying API layer functions for {}.".format(self.app_name))

            if runtime == "python" and type == "app":
                if self.compute_resource_group == self.web_resource_group:
                    raise Exception(
                        "Web Resource Group not set, or set incorrectly. Please "
                        "pass the --web_resource_group parameter when deploying a "
                        "Python Web App in the Api Layer!"
                    )

            app_settings = list()
            for endpoint in endpoints:
                # Get the source record from the sources table.
                # This helps to support shared sources, as well as partial deployments
                # during development.
                source_name = self.app_name + "-" + "endpoint" + "-" + endpoint["name"]
                try:
                    source_entry = self.table_service.get_entity(
                        self.source_table_name,
                        self.app_name,
                        source_name,
                    )
                except AzureMissingResourceHttpError as e:
                    logger.error(
                        "Failed to find source {} when deploying consumer groups "
                        "during real-time deployment.".format(source_name)
                    )
                    self.thread_exceptions.append(e)
                    raise e

                resource_group = source_entry.EventHubResourceGroup
                namespace = source_entry.EventHubNamespace
                # For ease of use in the bindings, we add an AppSetting for each source.
                # We also add an AppSetting for each Event Hub name to abstract it
                # from the end user.
                rule_keys = self.eh_client.namespaces.list_keys(
                    source_entry.EventHubResourceGroup,
                    source_entry.EventHubNamespace,
                    "send-key",
                )
                connection = rule_keys.primary_connection_string

                app_settings.append(
                    {"name": endpoint["name"] + "-connection", "value": connection}
                )
                app_settings.append(
                    {
                        "name": endpoint["name"] + "-eventhub",
                        "value": source_entry.EventHub,
                    }
                )
            if custom_secrets:
                for secret in custom_secrets:
                    secret_value = self.kv_client.get_secret(
                        "https://{key_vault_name}.vault.azure.net".format(
                            key_vault_name=self.key_vault
                        ),
                        secret["name"],
                        "",
                    ).value
                    if secret_value:
                        app_settings.append(
                            {
                                "name": secret["appSettingName"]
                                if "appSettingName" in secret
                                else secret["name"],
                                "value": secret_value,
                            }
                        )

            # Grabbing environment variables from .env file if it exists
            # and adding them as AppSettings.
            if self.environment in ["dev", "uat", "prd"]:
                env_fpath = Path(self.config_path + f"/{self.environment}.env.replace")
                logger.info(
                    f"Found environment file {env_fpath} for API layer. Adding AppSettings."
                )
            else:
                env_fpath = Path(self.config_path + "/sbx.env.replace")
                logger.info(f"No environment file found for API AppSettings.")

            if env_fpath.is_file():
                with open(env_fpath) as f:
                    f_content = f.read()
                config = ConfigParser()
                config.optionxform = str
                config.read_string(f_content)
                default_config = config["DEFAULT"]

                for key in default_config:
                    val = default_config[key]
                    app_settings.append({"name": key, "value": val})

            param_object = self.parameters_object.copy()
            param_object["DATABRICKS_TOKEN"] = {"value": self.databricks_token_prd}
            param_object["runtime"] = {"value": runtime}
            param_object["type"] = {"value": type}
            param_object["environment"] = {"value": self.compute_environment}
            if self.mdm_client_id:
                param_object["mdmClientId"] = {"value": self.mdm_client_id}
            if self.mdm_client_secret:
                param_object["mdmClientSecret"] = {"value": self.mdm_client_secret}
            param_object["keyVaultName"] = {"value": self.azure_key_vault}
            param_object["searchFlag"] = {"value": self.search_flag}
            param_object["signalRFlag"] = {"value": self.signalr_flag}
            param_object["sqlFlag"] = {"value": self.sql_flag}
            param_object["cosmosFlag"] = {"value": self.cosmos_flag}
            param_object["windowsResourceGroupName"] = {
                "value": self.compute_resource_group
            }
            if self.sql_flag:
                param_object["sqlAdministratorLogin"] = {"value": self.real_time_user}
                param_object["sqlAdministratorLoginPassword"] = {
                    "value": self.real_time_password
                }
            if self.databricks_token:
                param_object["databricksToken"] = {"value": self.databricks_token}
            # Because api_layer.json uses a nested template, we need to escape
            # by prepending "[" or Azure will attempt to evaluate it as an ARM
            # expression rather than a string
            param_object["emailReceivers"] = {
                "value": "[" + json.dumps(self.email_receivers)
            }
            param_object["eventHubSettings"] = {"value": app_settings}
            if asp_autoscale_settings:
                param_object["autoscaleEnabled"] = {"value": True}
                param_object["minimumCapacity"] = {
                    "value": asp_autoscale_settings["min_capacity"]
                }
                param_object["maximumCapacity"] = {
                    "value": asp_autoscale_settings["max_capacity"]
                }
                param_object["defaultCapacity"] = {
                    "value": asp_autoscale_settings["default_capacity"]
                }
            if sku:
                param_object["sku"] = {"value": sku}
            if hosting_plan:
                param_object["hostingPlan"] = {"value": hosting_plan}

            if type == "app":
                web_app_name = f"{self.org_name}-{self.region_code}-wa-udp-{self.app_name}-api-{self.environment}"
                try:
                    if runtime == "python":
                        existing_app_settings = self.web_client.web_apps.list_application_settings(
                            self.web_resource_group, web_app_name
                        )
                    else:
                        existing_app_settings = self.web_client.web_apps.list_application_settings(
                            self.compute_resource_group, web_app_name
                        )
                except AzureWebModels.DefaultErrorResponseException as e:
                    if e.inner_exception.error.code == "ResourceNotFound":
                        logger.info(
                            f"Existing {web_app_name} Web App instance was not found."
                        )
                        existing_app_settings = None
                        web_app_apigee_key = self.generate_random_apigee_key(
                            web_app_name
                        )
                        param_object["webAppKey"] = {"value": web_app_apigee_key}
                    else:
                        self.thread_exceptions.append(e)
                        raise e
                except Exception as e:
                    self.thread_exceptions.append(e)
                    raise e
                if existing_app_settings:
                    if existing_app_settings.properties.get("WebAppKey") is None:
                        web_app_apigee_key = self.generate_random_apigee_key(
                            web_app_name
                        )
                    else:
                        web_app_apigee_key = existing_app_settings.properties.get(
                            "WebAppKey"
                        )
                    param_object["webAppKey"] = {"value": web_app_apigee_key}

            if runtime == "python" and type == "app":
                param_object["webResourceGroup"] = {"value": True}
                # Azure has a limitation where special characters are not allowed in AppSetting names in a Linux environment
                for key in param_object["eventHubSettings"]["value"]:
                    key["name"] = re.sub("[^A-Za-z0-9]+", "_", key["name"])
                outputs = self.deploy_resource_template(
                    "api_layer", param_object, resource_group=self.web_resource_group
                )
                function_app_name = outputs["functionAppName"]["value"]
                self.deploy_function(
                    function_app_name,
                    self.api_path,
                    slot="s",
                    resource_group=self.web_resource_group,
                )
            else:
                outputs = self.deploy_resource_template(
                    "api_layer", param_object, compute=True
                )
                function_app_name = outputs["functionAppName"]["value"]
                function_key = self.deploy_function(
                    function_app_name, self.api_path, slot="s"
                )

            # Change Apigee endpoint:
            if self.deploy_apigee:
                if type == "functionapp":
                    logger.info("Switching Apigee endpoint to new Function App.")
                    self.apigee_client.update_endpoint(
                        self.app_name,
                        "https://{}.azurewebsites.net/api".format(function_app_name),
                        function_key,
                    )
                elif type == "app":
                    logger.info("Switching Apigee endpoint to new Web App.")
                    self.apigee_client.update_endpoint(
                        self.app_name,
                        "https://{}.azurewebsites.net/api".format(web_app_name),
                        web_app_apigee_key,
                    )

            logger.info(
                "API layer deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def get_function_app_key(self, function_app_name: str, master_key=False):
        """
        Deploy the API layer for an application.

        Args:
            function_app_name: The name of the Function App for which to retrieve the host key.

        Returns:
            The host key for the Function App.
        """
        logger.info(f"Retrieving Function App Host Key for {function_app_name}")
        try:
            # get publishing username and pw
            auth_response = self.web_client.web_apps.list_publishing_credentials(
                self.compute_resource_group, function_app_name, polling=True
            ).result()

            user = auth_response.publishing_user_name
            password = auth_response.publishing_password
            pair = user + ":" + password
            # convert user/pw to base 64 encoded string
            jwt_auth = base64.b64encode(pair.encode("ascii", "ignore")).decode("utf-8")
            jwt_header = {
                "Content-Type": "application/json",
                "Authorization": "Basic " + jwt_auth,
            }

            # use encoded user/pw to get JWT token
            jwt_uri = "https://{fa}.scm.azurewebsites.net/api/functions/admin/token".format(
                fa=function_app_name
            )
            jwt = requests.get(jwt_uri, headers=jwt_header)
            key_header = {
                "Content-Type": "application/json",
                "Authorization": "Bearer " + jwt.text.strip('"'),
            }

            # use JWT token as Bearer to get FA host key
            if (master_key==True):
                function_app_base_uri = (
                    f"https://{function_app_name}.azurewebsites.net/admin/host/systemkeys/_master"
                )
            else:
                function_app_base_uri = (
                    f"https://{function_app_name}.azurewebsites.net/admin/host/keys/default"
                )
            for attemptNumber in range(10):
                host_key = requests.get(function_app_base_uri, headers=key_header)
                if host_key.status_code in [200, 201]:
                    logger.info(
                        f"Host Key Retrieval Successful for {function_app_name}"
                    )
                    return host_key.json()["value"].strip()
                elif host_key.status_code == 503 and attemptNumber < 9:
                    logger.info(host_key.text)
                    logger.info(
                        f"Host Key Retrieval unsuccessful for app {function_app_name} - retry {attemptNumber + 1}/10. Status {host_key.status_code}"
                    )
                    time.sleep(20)
                else:
                    logger.error(f"Host Key Retrieval Failed for {function_app_name}")
                    raise Exception(
                        f"Function App Key Retrieval Failed: {host_key.status_code}"
                    )
        except Exception as e:
            logger.error(e)
            raise Exception("Function App Key Retrieval Failed")

    def deploy_tester(self):
        deploy_resource_group = self.compute_resource_group
        param_object = self.parameters_object.copy()

        # Deploy tester ARM resource template
        logger.info("Deploying tester app resource template in main location")
        outputs = self.deploy_resource_template(
            "api_tester", param_object,
            resource_group=deploy_resource_group
        )
        logger.info("Deployment successful")

        # Deploy code as ZIP file package
        logger.info("Deploying tester app code in main location")
        function_app_name = outputs["functionAppName"]["value"]
        self.deploy_function(
            function_app_name,
            "{}/tester/".format(self.shared_functions_base_path),
            resource_group=deploy_resource_group
        )
        logger.info("Deployment successful")

        # Get key for tester function app
        logger.info("Retrieving key for tester function app")
        function_app_key = self.get_function_app_key(function_app_name, master_key=True)
        logger.info("Retrieval successful")

        # Construct and return tester function app URL
        route = "v1/apitester"
        tester_url = f"https://{function_app_name}.azurewebsites.net/api/{route}?code={function_app_key}"
        return tester_url

    def generate_random_apigee_key(self, web_app_name: str):
        """
        Generate a random base64-encoded token for a Web App to be used with Apigee.

        Args:
            web_app_name: The name of the Web App for which to generate an Apigee key.

        Returns:
            The apigee key for the Web App.
        """
        logger.info(f"Generating random Apigee key for the {web_app_name} Web App.")
        apigee_key = secrets.token_urlsafe(16)
        return apigee_key

    def deploy_ingestion_function(self, source_type: str):
        """Deploy any ingestion function that uses the BaseIngestion class."""
        ingestion_class = ingestion_types[source_type]
        function_type = ingestion_class.get_source_type()
        arm_template_name = f"{function_type}_ingestion"
        if ingestion_class.REQUIRES_WEB_RG:
            resource_group = self.web_resource_group
        else:
            resource_group = self.compute_resource_group
        code_path = Path(
            self.shared_functions_base_path,
            function_type + "_ingestion"
        )

        logger.info(
            f"Deploying {function_type} ingestion for app {self.app_name}."
        )

        # Creating the path variables and zipping code.
        code_sas_url = self._deploy_function_to_blob(function_type, code_path)

        # Set up parameters for the ARM template
        param_object = self.parameters_object.copy()
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["keyVaultName"] = {"value": self.azure_key_vault}
        param_object["dlResourceGroup"] = {"value": self.udp_resource_group}
        param_object["baseResourceGroup"] = {
            "value": self.compute_resource_group}
        param_object["codeSas"] = {"value": code_sas_url}
        param_object["emailReceivers"] = {
            "value": json.dumps(self.email_receivers)
        }
        vnet: typing.Optional[typing.Dict[str, str]] = None
        if ingestion_class.USE_VNET:
            vnet = defaults.asp_vnet_injection_map.get(
                self.app_name, dict()
            ).get(
                self.location, dict()
            ).get(
                self.compute_environment, dict()
            ).get(
                'vnet', None
            )
        if vnet is not None:
            logger.info(
                f'Using VNet {vnet["vnetName"]} with subnet '
                f'{vnet["subnetName"]} for {function_type} ingestion'
            )
            param_object["vnetConnection"] = {"value": vnet}

        outputs = self.deploy_resource_template(
            arm_template_name, param_object,
            resource_group=resource_group
        )
        function_app_name = outputs["functionAppName"]["value"]

        # Sync Function triggers
        self._sync_function_triggers(function_app_name, resource_group)
        if self.dr_flag:
            # Deploy in East US 2 for disaster recovery
            logger.info(f"Deploying {function_type} ingestion to DR location")
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}
            dr_param_object["environment"] = {"value": self.compute_environment}
            dr_vnet: typing.Optional[typing.Dict[str, str]] = None
            if ingestion_class.USE_VNET:
                dr_vnet = defaults.asp_vnet_injection_map.get(
                    self.app_name, dict()
                ).get(
                    self.dr_location, dict()
                ).get(
                    self.compute_environment, dict()
                ).get(
                    'vnet', None
                )
            if dr_vnet is None:
                # Remove VNet config, if it exists from above
                _ = dr_param_object.pop('vnetConnection', None)
            else:
                logger.info(
                    f'Using DR VNet {dr_vnet["vnetName"]} with subnet '
                    f'{dr_vnet["subnetName"]} for {function_type} ingestion'
                )
                dr_param_object["vnetConnection"] = {"value": dr_vnet}

            outputs_dr = self.deploy_resource_template(
                arm_template_name,
                dr_param_object,
                resource_group=resource_group
            )
            function_app_name_dr = outputs_dr["functionAppName"]["value"]

            # Sync Function triggers
            self._sync_function_triggers(function_app_name_dr, resource_group)

    # TODO Move to ingestion classes
    def deploy_api_ingestion(self):
        """
        Deploy the API ingestion capability for the application.
        """
        logger.info("Deploying API ingestion for {}.".format(self.app_name))
        param_object = self.parameters_object.copy()
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["keyVaultName"] = {"value": self.azure_key_vault}
        param_object["namespaceKeys"] = {
            "value": [
                {
                    "name": "EventHub{}Connection".format(x["index"]),
                    "value": x["send_key"],
                }
                for x in self.event_hub_namespaces
            ]
        }

        logger.info("Deploying api http function app to main location")
        outputs = self.deploy_resource_template(
            "api_http_function_app_arm", param_object, compute=True
        )
        self.api_ingestion_queue_conn = outputs["apiQueueConnectionString"]["value"]
        logger.info(
            "Vaulting API ingestion queue connection to {} key vault".format(
                self.azure_key_vault
            )
        )
        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "api-ingestion-queue-conn",
            outputs["apiQueueConnectionString"]["value"],
        )
        function_app_name = outputs["functionAppName"]["value"]
        logger.info("Deploy api ingestion code in main location")
        if os.path.exists(
            "{}/configurable_api_ingestion/build.zip".format(
                self.shared_functions_base_path
            )
        ):
            os.remove(
                "{}/configurable_api_ingestion/build.zip".format(
                    self.shared_functions_base_path
                )
            )
        self.deploy_function(
            function_app_name,
            "{}/configurable_api_ingestion/".format(self.shared_functions_base_path),
        )

        if self.dr_flag:
            # Deploy in DR location
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}

            logger.info("Deploying api http function app to DR location")
            output_dr = self.deploy_resource_template(
                "api_http_function_app_arm", dr_param_object, compute=True
            )
            self.api_ingestion_queue_conn_dr = output_dr["apiQueueConnectionString"][
                "value"
            ]
            logger.info(
                "Vaulting API ingestion queue connection to {} key vault".format(
                    self.azure_key_vault_dr
                )
            )
            self.kv_client.set_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault_dr
                ),
                "api-ingestion-queue-conn",
                output_dr["apiQueueConnectionString"]["value"],
            )
            function_app_name_dr = output_dr["functionAppName"]["value"]

            logger.info("Deploy api ingestion code in DR location")
            self.deploy_function(
                function_app_name_dr,
                "{}/configurable_api_ingestion/".format(
                    self.shared_functions_base_path
                ),
            )

    # Delete any orphaned databases from previous deployments
    def delete_orph_dbs(self, deployed_db_list):
        curr_db_iter = self.sql_client.databases.list_by_server(
            self.resource_group, self.real_time_server
        )
        curr_db_list = []
        for curr_db in curr_db_iter:
            curr_db_list.append(curr_db.name)
        orph_db_list = list(set(curr_db_list) - set(deployed_db_list) - set(["master"]))
        for orph_db in orph_db_list:
            self.sql_client.databases.delete(
                self.resource_group, self.real_time_server, orph_db
            ).result()
        return orph_db_list

    def create_schema_versions_table(self, cursor):
        cursor.execute("""if not exists (select * from sysobjects where name='SchemaVersions' and xtype='U') create table SchemaVersions (Id INT IDENTITY PRIMARY KEY, ScriptName nvarchar(256) NOT NULL, Applied datetime NOT NULL)""")
        cursor.commit()

    def check_schema_versions(self, sql_file, cursor):
        cursor.execute("""select * from SchemaVersions where ScriptName = '{}'""".format(sql_file))
        result = cursor.fetchall()
        if len(result) == 0:
            return False
        return True

    def execute_sql_file(self, file_path, cursor):
        with open(file_path, 'r') as file:
            sql = file.read()
            try:
                for sql_statement in sql.split(';'):
                    if sql_statement.strip() == "":
                        continue
                    else:
                        cursor.execute(f"{sql_statement};")
            except Exception as e:
                logger.error(
                    f'Could not execute SQL file: {file_path}.  '
                    f'Changes were rolled back.'
                )
                cursor.rollback()
                self.thread_exceptions.append(e)
                raise e
            cursor.commit()

    def update_schema_versions(self, sql_file, cursor):
        cursor.execute(f"""insert into SchemaVersions (ScriptName, Applied) values ('{sql_file}', CURRENT_TIMESTAMP)""")
        cursor.commit()

    def execute_db_sql(self, conn_str, sql_path, database):
        conn = pyodbc.connect(conn_str)
        cursor = conn.cursor()
        self.create_schema_versions_table(cursor)
        for sql_file in sorted([os.path.basename(x) for x in glob.glob(f"{sql_path}/*.sql")]):
            file_already_ran = self.check_schema_versions(sql_file, cursor)
            if not file_already_ran:
                logger.info(f"Executing {sql_file} script on {database} database.")
                file_path = os.path.join(sql_path, sql_file)
                self.execute_sql_file(file_path, cursor)
                self.update_schema_versions(sql_file, cursor)
                logger.info(f"Successfully executed {sql_file} script on {database} database.")
            else:
                logger.info(f"Script {sql_file} already executed on {database} database - skipping.")
                continue

    def deploy_azure_sql(self, databases):
        thread = threading.Thread(target=self._deploy_azure_sql, args=[databases])
        thread.start()
        self.data_store_threads.append(thread)

    def _deploy_azure_sql(self, databases):
        """
        Deploy an Azure SQL DB.
        """
        t = time.time()
        try:
            logger.info(
                "Deploying SQL files from app to Azure SQL DB {}.".format(
                    self.real_time_server
                )
            )
            # If a SQL path is set, deploy the SQL scripts to the DB with DbUp
            if self.sql_path:
                logger.info(
                    "Deploying SQL scripts for {} from {}.".format(
                        self.app_name, self.sql_path
                    )
                )

                # Check for subfolders in SQL path. If there are subfolders, assume
                # the subfolders are named after the databases and attempt to deploy.
                # If there are no subfolders, check the length of the databases object
                # and fail if it's greater than one. Create a tuple of path/db
                # combinations to loop through.
                subdirs = next(os.walk(self.sql_path))[1]
                if len(subdirs) == 0 and len(databases) == 1:
                    logger.info(
                        "Found a single database and no subfolders in the SQL path. Deploying scripts from that directory."
                    )
                    path_tuples = [(self.sql_path, databases[0]["databaseName"])]
                # If there is more than one DbUp folder or more than one DB, they
                # must match.
                elif (len(subdirs) > 0 or len(databases) > 1) and len(subdirs) == len(
                    databases
                ):
                    path_tuples = []
                    # Check to make sure each database in the config has a DbUp path.
                    for database in databases:
                        database_name = database["databaseName"]
                        db_sql_path = f"{self.sql_path}/{database_name}"
                        if not os.path.exists(db_sql_path):
                            logger.error(
                                f"Could not find a subfolder in {self.sql_path} for DB {database_name}."
                            )
                            raise SQLFolderNotFound("Missing SQL path.")
                        else:
                            path_tuples.append((db_sql_path, database_name))

                else:
                    logger.error(
                        "Database subfolders in DbUp path did not match databases in config."
                    )
                    logger.error(
                        f"Found {len(subdirs)} DbUp folders and {len(databases)} databases."
                    )
                    raise Exception("SQL deployment failed.")

                sql_ad_admin_email = defaults.SQL_AD_ADMIN_EMAIL
                sql_ad_admin_password = self.kv_client.get_secret(
                    "https://{key_vault_name}.vault.azure.net".format(
                        key_vault_name=self.key_vault
                    ),
                    "udpsvcazdatabricks",
                    "",
                ).value

                for path_tuple in path_tuples:
                    db_sql_path = path_tuple[0]
                    database_name = path_tuple[1]
                    connection_string = "Driver={{ODBC Driver 17 for SQL Server}};Server=tcp:{0}.database.windows.net;Port=1433;DATABASE={1};UID={2};PWD={3};Authentication=ActiveDirectoryPassword;".format(
                        self.real_time_server,
                        database_name,
                        sql_ad_admin_email,
                        sql_ad_admin_password,
                    )
                    self.execute_db_sql(connection_string, db_sql_path, database_name)

                deployed_db_list = list(map(lambda x: x[1], path_tuples))
                deleted_dbs = self.delete_orph_dbs(deployed_db_list)

            logger.info(
                "Azure SQL deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def deploy_azure_cosmos(self, databases):
        thread = threading.Thread(target=self._deploy_azure_cosmos, args=[databases])
        thread.start()
        self.data_store_threads.append(thread)

    def _deploy_azure_cosmos(self, databases):
        """
        Deploy an Azure Cosmos DB.
        """
        t = time.time()
        try:
            logger.info("Deploying Azure Cosmos DB for {}.".format(self.app_name))
            logger.info("Creating Cosmos client and publishing stored procs.")
            self.cosmos_client = CosmosClient(
                url_connection=self.cosmos_url, auth={"masterKey": self.cosmos_key}
            )
            with open(
                "{}/../../js/cosmos_update.js".format(SCRIPT_DIRECTORY), "r"
            ) as update_proc:
                update_proc_content = update_proc.read()
            sproc_definition = {"id": "spUpdate", "serverScript": update_proc_content}

            for database_info in databases:
                for container in database_info["containers"]:
                    try:
                        proc = self.cosmos_client.CreateStoredProcedure(
                            "dbs/{}/colls/{}".format(
                                database_info["databaseName"],
                                container["containerName"],
                            ),
                            sproc_definition,
                        )
                    except HTTPFailure as e:
                        proc = self.cosmos_client.ReplaceStoredProcedure(
                            "dbs/{}/colls/{}/sprocs/spUpdate".format(
                                database_info["databaseName"],
                                container["containerName"],
                            ),
                            {"id": "spUpdate", "body": update_proc_content},
                        )

            param_object = self.parameters_object.copy()
            param_object["dlResourceGroup"] = {"value": self.udp_resource_group}
            param_object["namespaceKeys"] = {
                "value": [
                    {
                        "name": "EventHub{}Connection".format(x["index"]),
                        "value": x["send_key"],
                    }
                    for x in self.event_hub_namespaces
                ]
            }

            outputs = self.deploy_resource_template(
                "cosmos_capture", param_object, compute=True
            )

            function_app_name = outputs["functionAppName"]["value"]

            self.deploy_function(
                function_app_name,
                "{}/cosmos_capture/".format(self.shared_functions_base_path),
            )

            self.deploy_function(
                self.utils_app_name,
                "{}/cosmos_autoscale/".format(self.shared_functions_base_path),
            )

            logger.info(
                "Cosmos DB deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def deploy_dll(self):
        """
        Deploy the data lake load functions for the application.
        """
        logger.info("Deploying data lake loads for {}".format(self.app_name))
        if os.path.exists(
            "{}/data_lake_load/build.zip".format(self.shared_functions_base_path)
        ):
            os.remove(
                "{}/data_lake_load/build.zip".format(self.shared_functions_base_path)
            )

        param_object = self.parameters_object.copy()
        param_object["dlResourceGroup"] = {"value": self.udp_resource_group}
        param_object["namespaceKeys"] = {
            "value": [
                {
                    "name": "EventHub{}Connection".format(x["index"]),
                    "value": x["listen_key"],
                }
                for x in self.event_hub_namespaces
            ]
        }

        outputs = self.deploy_resource_template(
            "data_lake_load", param_object, compute=True
        )

        function_app_name = outputs["functionAppName"]["value"]
        self.deploy_function(
            function_app_name,
            "{}/data_lake_load/".format(self.shared_functions_base_path),
        )

    # TODO Move to ingesion classes
    def deploy_db_ingestion(self, networking: object = None):
        """
        Deploy the DB ingestion capability for the application.
        """
        logger.info("Deploying DB ingestion for {}.".format(self.app_name))
        param_object = self.parameters_object.copy()
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["keyVaultName"] = {"value": self.azure_key_vault}
        param_object["dbConnectionTimeout"] = {"value": self.db_connection_timeout}
        param_object["namespaceKeys"] = {
            "value": [
                {
                    "name": "EventHub{}Connection".format(x["index"]),
                    "value": x["send_key"] + ";OperationTimeout=0:02:00;",
                }
                for x in self.event_hub_namespaces
            ]
        }

        param_object["singleAspFlag"] = {"value": self.singleAspFlag}

        if networking:
            if networking["vnet"]:
                logger.info("Deploying DB ingestion with VNet Connection VNet = "+ networking["vnet"]["vnetName"] +" and Subnet = "+networking["vnet"]["subnetName"] )
                param_object["vnetConnection"] = {"value": networking["vnet"]}

        logger.info("Deploying DB ingestion to main location")
        outputs = self.deploy_resource_template(
            "db_ingestion_function_app_arm", param_object, compute=True
        )

        function_app_name = outputs["functionAppName"]["value"]
        if os.path.exists(
            "{}/configurable_db_ingestion/build.zip".format(
                self.shared_functions_base_path
            )
        ):
            os.remove(
                "{}/configurable_db_ingestion/build.zip".format(
                    self.shared_functions_base_path
                )
            )
        self.deploy_function(
            function_app_name,
            "{}/configurable_db_ingestion/".format(self.shared_functions_base_path),
        )

        if self.dr_flag:
            # Deploy in East US 2 for disaster recovery
            logger.info("Deploying db ingestion to DR location")
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}
            dr_param_object["environment"] = {"value": self.compute_environment}
            dr_param_object["environment"] = {"value": self.compute_environment}
            dr_param_object["dbConnectionTimeout"] = {"value": self.db_connection_timeout}
            output_dr = self.deploy_resource_template(
                "db_ingestion_function_app_arm", dr_param_object, compute=True
            )
            function_app_name_dr = output_dr["functionAppName"]["value"]
            self.deploy_function(
                function_app_name_dr,
                "{}/configurable_db_ingestion/".format(self.shared_functions_base_path),
            )

    def create_db_users(self, cwd):
        # run SQL script adding AAD members to the SQL dbmanager role

        server = (
            self.parameters_object["orgName"]["value"]
            + self.parameters_object["environment"]["value"]
            + self.parameters_object["projectName"]["value"]
            + "sqlserver.database.windows.net"
        )
        driver = "{ODBC Driver 17 for SQL Server}"
        conn_str = "Driver={driver};Server={server};PORT=1433;DATABASE={db};UID=;Authentication=ActiveDirectoryInteractive".format(
            driver=driver, server=server, db="master"
        )
        conn = pyodbc.connect(conn_str)
        cursor = conn.cursor()

        try:
            with open(cwd + "\\sql\\add_db_roles.sql", "r") as sql_script:
                sql_commands = []
                for line in sql_script:
                    sql_commands.append(line)

                for command in sql_commands:
                    if command:
                        logger.info("Executing command: {c}.".format(c=command))
                        cursor.execute(command)
                        logger.info(
                            "Command: {c} successfully executed.".format(c=command)
                        )

                logger.info("All AAD users added to dbmanager role.")
        except Exception as e:
            logger.info(e)

    def deploy_batchfile_transformation(self, databricks_token):
        """
        Deploy batchfile ingestion and transformation code.
        This Azure Function is running the Linux consumption plan,
        which requires running from package. The method pushes the
        zip to the app blob storage account and creates a SAS, then
        deploys the template which points the Function app to the
        SAS token.

        Args:
            databricks_token: The Databricks token used to trigger the jobs.
        """
        function_type = "batchfile"
        logger.info(
            "Deploying {} transformation for app {}.".format(
                function_type, self.app_name
            )
        )

        # Deploying blob-events queue for batch file ingestion.
        queue_service_client = QueueServiceClient(account_url=f"https://{self.app_storage_name}.queue.core.windows.net/", credential=self.app_storage_key)
        try:
            queue_service_client.create_queue("blob-events")
        except ResourceExistsError:
            logger.info("Blob events queue already exists.")

        # Creating the path variables and zipping code.
        code_path = Path(
            self.shared_functions_base_path,
            function_type + "_ingestion"
        )
        code_sas_url = self._deploy_function_to_blob(function_type, code_path)

        param_object = self.parameters_object.copy()
        param_object["location"] = {"value": self.location}
        param_object["regionCode"] = {"value": self.region_code}
        param_object["environment"] = {"value": self.compute_environment}
        param_object["keyVaultName"] = {"value": self.azure_key_vault}
        param_object["databricksToken"] = {"value": databricks_token}
        param_object["appResourceGroup"] = {"value": self.resource_group}
        param_object["udpResourceGroup"] = {"value": self.udp_resource_group}
        param_object["snapSchedulerJobs"] = {"value": ';'.join(self.snapshot_scheduler_jobs)}
        param_object["codeSas"] = {"value": code_sas_url}

        outputs = self.deploy_resource_template(
            "batch_file_transformation_function_app_arm", param_object,
            resource_group=self.web_resource_group,
        )
        logger.info(
            "Vaulting batch file ingestion queue connection to {} key vault".format(
                self.azure_key_vault
            )
        )
        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "batchfile-queue-storage-connection",
            outputs["batchfileQueueStorageConnection"]["value"],
        )
        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "landing-account-name",
            outputs["landingAccountName"]["value"],
        )
        self.kv_client.set_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.azure_key_vault
            ),
            "landing-account-key",
            outputs["landingAccountKey"]["value"],
        )
        function_app_name = outputs["functionAppName"]["value"]
        # queue_storage_name = outputs["queueStorageAccountName"]["value"]

        # Syncing the Function triggers.
        self._sync_function_triggers(
            function_app_name, self.web_resource_group
        )

        if self.dr_flag:
            # Deploy in East US 2 for disaster recovery
            logger.info("Deploying batch file transformation to DR location")
            dr_param_object = param_object.copy()
            dr_param_object["location"] = {"value": self.dr_location}
            dr_param_object["regionCode"] = {"value": self.dr_region_code}
            dr_param_object["environment"] = {"value": self.compute_environment}
            output_dr = self.deploy_resource_template(
                "batch_file_transformation_function_app_arm",
                dr_param_object,
                resource_group=self.web_resource_group,
            )
            logger.info(
                "Vaulting batch file ingestion queue connection to {} key vault".format(
                    self.azure_key_vault_dr
                )
            )
            self.kv_client.set_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault_dr
                ),
                "batchfile-queue-storage-connection",
                output_dr["batchfileQueueStorageConnection"]["value"],
            )
            function_app_name_dr = output_dr["functionAppName"]["value"]
            # queue_storage_name_dr = output_dr["queueStorageAccountName"]["value"]
            # Syncing the Function triggers.
            self._sync_function_triggers(
                function_app_name_dr, self.web_resource_group
            )

    def deploy_dbricks_sql_user(self, workspace_name, secret_client, secret_scope, sql_login, sql_user):
        """
        Deploy a new SQL user and grant that user read-only access to the Azure SQL DB
        """
        server = f"{self.org_name}-{self.region_code}-sql-udp-{self.app_name}-{self.environment}.database.windows.net"
        driver = "{ODBC Driver 17 for SQL Server}"

        sql_password = self.get_or_generate_sql_password(self.azure_key_vault, "sql-reader-login-password", set_secret=True)

        try:
            conn_str = f"Driver={driver};Server={server};PORT=1433;DATABASE=master;UID={self.real_time_user};PWD={self.real_time_password}"
            conn = pyodbc.connect(conn_str, autocommit=True)
            cursor = conn.cursor()
            sql_master_command = f"""
            IF NOT EXISTS (SELECT name FROM sys.sql_logins WHERE name='{sql_login}')
                CREATE LOGIN {sql_login} WITH PASSWORD='{sql_password}';
            ELSE
                SELECT('Found Login for {sql_login}!')
            """
            cursor.execute(sql_master_command)
            conn.close()

            if self.sql_databases:
                databases = [database["databaseName"] for database in self.sql_databases]
                for database in databases:
                    conn_str = f"Driver={driver};Server={server};PORT=1433;DATABASE={database};UID={self.real_time_user};PWD={self.real_time_password}"
                    conn = pyodbc.connect(conn_str, autocommit=True)
                    cursor = conn.cursor()
                    sql_reader_user_command = f"""
                    IF DATABASE_PRINCIPAL_ID('{sql_user}') IS NULL
                        CREATE USER {sql_user} FOR LOGIN {sql_login};
                    """
                    sql_reader_role_command = f"""
                    ALTER ROLE db_datareader ADD MEMBER {sql_user};
                    """
                    cursor.execute(sql_reader_user_command)
                    if database != "master":
                        cursor.execute(sql_reader_role_command)
                    conn.close()
                logger.info("Successfully granted read-only role to Azure SQL database(s)!")
        except Exception as e:
            raise e

        secret_client.set_secret(secret_scope, "sqldbserver", self.real_time_server)
        # Only adding SQL Database secret if there's only one database.
        if len(self.sql_databases) == 1:
            secret_client.set_secret(secret_scope, "sqldbreaderdatabase", self.real_time_database)
        secret_client.set_secret(secret_scope, "sqldbreaderuser", sql_login)
        secret_client.set_secret(secret_scope, "sqldbreaderpassword", sql_password)

    def deploy_dbricks_disco(self):
        thread = threading.Thread(target=self._deploy_dbricks_disco)
        thread.start()
        self.threads.append(thread)

    def _deploy_dbricks_disco(self):
        """
        Deploy a Databricks Discovery Workspace.
        """
        t = time.time()
        try:
            logger.info(
                "Deploying Databricks Discovery Workspace for app {}.".format(
                    self.app_name
                )
            )
            param_object = self.parameters_object.copy()
            param_object["location"] = {"value": self.location}
            param_object["regionCode"] = {"value": self.region_code}
            param_object["locationDr"] = {"value": self.dr_location}
            param_object["regionCodeDr"] = {"value": self.dr_region_code}

            logger.info(
                "Deploying Databricks Discovery Workspaces to main and DR locations"
            )
            outputs = self.deploy_resource_template(
                "databricks_discovery_workspace", param_object
            )
            workspace_name = outputs["workspaceName"]["value"]
            workspace_name_prd = workspace_name[:-3] + 'prd'
            logger.info("Creating Databricks secret scope for databricks discovery")
            header = self.get_databricks_header(workspace_name)
            # creating and adding databricks_token for ml workflow
            self.databricks_token_prd = self.create_databricks_token_prd(workspace_name_prd)
            secret_client = DatabricksSecretClient(
                "https://{}.azuredatabricks.net".format(self.location), header
            )
            secret_scope = "udp-infra"
            secret_client.create_scope(secret_scope)
            secret_client.set_secret(secret_scope, "environment", self.environment)
            secret_client.set_secret(
                secret_scope, "datalakeaccount", self.lake_account_name
            )
            secret_client.set_secret(
                secret_scope, "cosmosconnectionurl", self.cosmos_url
            )
            secret_client.set_secret(
                secret_scope, "cosmosconnectionkey", self.cosmos_key_read_only
            )
            secret_client.set_secret(
                secret_scope,
                "datalakepathraw",
                "abfss://raw@{}.dfs.core.windows.net/".format(self.lake_account_name),
            )
            secret_client.set_secret(
                secret_scope,
                "datalakepathprocessed",
                "abfss://processed@{}.dfs.core.windows.net/".format(
                    self.lake_account_name
                ),
            )

            logger.info("Creating shared access signature for Table Service")
            expiry_date = dt.utcnow() + timedelta(days=90)
            resource_types = ResourceTypes(object=True)
            account_permissions = AccountSasPermissions(read=True)
            sas_token = self.table_service.generate_account_shared_access_signature(
                resource_types, account_permissions, expiry_date, protocol="https"
            )

            secret_client.set_secret(secret_scope, "catalogsas", sas_token)

            if self.sql_flag:
                logger.info(f"Granting read-only Azure SQL DB access in the {workspace_name} disco workspace for the {self.app_name} app.")
                sql_login = "discoReader"
                sql_user = "discoReaderUser"
                self.deploy_dbricks_sql_user(workspace_name, secret_client, secret_scope, sql_login, sql_user)
            else:
                logger.info(f"No Azure SQL DB found for {self.app_name}; not granting read-only SQL access to the {workspace_name}.")

            logger.info(
                "Databricks disco deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )

        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def deploy_dbricks_batch(
        self, pricing_tier: str, batch_file_sources=[], batch_jobs=[], region_code=None
    ):
        thread = threading.Thread(
            target=self._deploy_dbricks_batch,
            args=[pricing_tier],
            kwargs={"batch_file_sources": batch_file_sources, "batch_jobs": batch_jobs, "region_code": region_code},
        )
        thread.start()
        self.batch_threads.append(thread)

    def _deploy_dbricks_batch(
        self, pricing_tier: str, batch_file_sources=[], batch_jobs=[], region_code=None
    ):
        """
        Deploy a Databricks Batch Workspace
    
        Args:
            pricing tier: azure pricing tier for Databricks Workspace
        """
        t = time.time()
        try:
            logger.info(
                "Deploying Databricks Batch Workspace for app {}.".format(self.app_name)
            )
            if not region_code:
                region_code = self.region_code
            param_object = self.parameters_object.copy()
            param_object["location"] = {"value": self.location}
            param_object["regionCode"] = {"value": self.region_code}
            param_object["locationDr"] = {"value": self.dr_location}
            param_object["regionCodeDr"] = {"value": self.dr_region_code}
            param_object["pricingTier"] = {"value": pricing_tier}
            param_object["environment"] = {"value": self.compute_environment}

            # Check the map for the current application.
            app_map = defaults.dbricks_vnet_injection_map.get(self.app_name)

            # Deploy in centralus region only.
            # TODO: Once VNET is enalbed in westeurope remove location check.
            if app_map and self.environment in ["dev", "uat", "prd"] :
                logger.info(
                    f"Application {self.app_name} marked for Databricks VNet Injection."
                )
                try:
                    vnetName = app_map[self.location][self.environment]["vnetName"]
                    baseCidr = app_map[self.location][self.environment]["baseCidr"]
                    private_cidr = app_map[self.location][self.environment]["private_cidr"]
                    public_cidr = app_map[self.location][self.environment]["public_cidr"]
                except KeyError:
                    logger.info(
                        f"Using sandbox network configuration for VNet injection."
                    )
                    vnetName = app_map["centralus"]["sbx"]["vnetName"]
                    baseCidr = app_map["centralus"]["sbx"]["baseCidr"]
                    private_cidr = app_map["centralus"]["sbx"]["private_cidr"]
                    public_cidr = app_map["centralus"]["sbx"]["public_cidr"]

                # Deploying the subnets, NSGs, and RTs.
                logger.info(
                    f"Deploying public/private VNet {vnetName} pairs with CIDRs {private_cidr} and {public_cidr}."
                )
                vnet_params = self.parameters_object.copy()
                vnet_params["vnetName"] = {"value": vnetName}
                vnet_params["baseCidr"] = {"value": baseCidr}
                vnet_params["location"] = {"value": self.location}
                vnet_params["privateSubnetCidr"] = {"value": private_cidr}
                vnet_params["publicSubnetCidr"] = {"value": public_cidr}
                outputs = self.deploy_resource_template(
                    "databricks_network",
                    vnet_params,
                    resource_group=self.network_resource_group,
                )

                param_object["vnetFlag"] = {"value": True}
                param_object["vnetName"] = {"value": outputs["vnetName"]["value"]}
                param_object["privateSubnetName"] = {"value": outputs["privateSubnetName"]["value"]}
                param_object["publicSubnetName"] = {"value": outputs["publicSubnetName"]["value"]}

            logger.info(
                "Deploying Databricks Batch Workspace for app {}.".format(self.app_name)
            )

            # Retry logic for databricks workspace deployment
            retry_count = 3
            retry_databricks_batch_workspace = int(0)
            while retry_databricks_batch_workspace < int(retry_count):
                retry_databricks_batch_workspace += 1
                logger.info(
                    "Attempt {} to deploy Databricks workspace".format(
                        retry_databricks_batch_workspace
                    )
                )
                try:
                    outputs = self.deploy_resource_template(
                        "databricks_batch_workspace", param_object, compute=True
                    )
                    logger.info("Databricks workspace deployment was successful.")
                    break
                except CloudError as e:
                    if (
                        retry_databricks_batch_workspace < int(retry_count)
                        and e.status_code == 500
                    ):
                        continue
                    else:
                        raise e

            # Retrieving the values for the application's service principal.
            if self.environment in ["prod", "uat", "sit", "dev"]:
                key_vault_env = self.environment
            else:
                key_vault_env = "sbx"

            workspace_name = outputs["workspaceName"]["value"]
            self.databricks_token = self.create_databricks_token(workspace_name)

            snapshot_scheduler = self.deploy_batch_jobs(
                self.databricks_token,
                workspace_name,
                app_client_id=self.app_client_id,
                app_client_secret=self.app_client_secret,
                batch_file_sources=batch_file_sources,
                batch_jobs=batch_jobs,
                alerting=self.alerting,
            )

            if len(batch_file_sources) > 0 or snapshot_scheduler:
                self.deploy_batch_sources(
                    self.databricks_token, batch_file_sources
                )

            logger.info(
                "Databricks batch deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )

        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

        #Deploy users and group to Databricks workspace
        ad_automate = DatabricksWorkspace(
            "https://{}.azuredatabricks.net".format(self.location),
            workspace_name,
            self.databricks_token,
            self.app_ad_group_id,
            defaults.DATABRICKS_GROUP_NAME
        )
        ad_automate.create_databricks_ad_groups()
        ad_automate.extract_databricks_ad_users()
        ad_automate.add_databicks_ad_users()
            
    def deploy_databricks_library(
        self,
        databricks_token,
        workspace,
        dbfs_lib_path,
        wheel_path=None,
        dbfs_file_name=None,
    ):
        header = {"Authorization": "Bearer {}".format(databricks_token)}
        lib_name = os.path.basename(dbfs_lib_path)
        fs_client = DatabricksFS(
            "https://{}.azuredatabricks.net".format(self.location), header
        )
        dbfs_lib_dir = os.path.dirname(dbfs_lib_path)
        if not wheel_path:
            wheel_path = self.python_lib_path + "/" + lib_name

        try:
            fs_client.mkdirs(dbfs_lib_dir)
            fs_client.put(
                dbfs_lib_dir,
                wheel_path,
                streaming=True,
                overwrite=True,
                file_name=dbfs_file_name,
            )
        except Exception as e:
            logger.error(e)
            try:
                logger.error(e.response.text)
            except AttributeError:
                pass
            self.thread_exceptions.append(e)
            raise

    def deploy_databricks_job(
        self,
        fs_client,
        databricks_token,
        workspace,
        job_name,
        python_file,
        libraries=[],
        parameters=None,
        schedule=None,
        environment_variables={},
        max_retries=None,
        min_retry_interval_millis=None,
        max_concurrent_runs=None,
        email_notifications=None,
        cluster_user_config={},
        snapshot_scheduler=False,
    ):
        """
        Deploy a PySpark Databricks job with code.
        If a job with the same name exists, the job will be updated.

        Args:
            job_name: The name of the job to deploy
            python_file: The path to the Python code to deploy as the job

        Returns:
            The ID of the created or updated job.
        """
        header = {"Authorization": "Bearer {}".format(databricks_token)}

        spark_conf = '{"spark.databricks.cluster.profile":"serverless", "spark.databricks.repl.allowedLanguages":"sql,python"}'
        spark_ver = cluster_user_config.get("spark_version", defaults.DBRICKS_DEFAULT_RUNTIME)
        node_type_id = "Standard_DS3_v2"
        custom_tags = '{"ResourceClass":"Serverless"}'
        cluster_configs = {
            "spark_version": spark_ver,
            "node_type_id": node_type_id,
            "num_workers": 2,
            "spark_env_vars": environment_variables,
        }

        # Override default cluster configurations if set by the user
        if cluster_user_config.get("node_type_id"):
            cluster_configs["node_type_id"] = cluster_user_config["node_type_id"]
        if cluster_user_config.get("num_workers"):
            cluster_configs["num_workers"] = cluster_user_config["num_workers"]
        elif cluster_user_config.get(
            "autoscale_min_workers"
        ) and cluster_user_config.get("autoscale_max_workers"):
            cluster_configs["autoscale"] = {
                "min_workers": cluster_user_config["autoscale_min_workers"],
                "max_workers": cluster_user_config["autoscale_max_workers"],
            }
            del cluster_configs["num_workers"]

        try:
            fs_client.put("dbfs:/batch_code/", python_file, overwrite=True)
            job = DatabricksJob(
                job_name,
                "https://{}.azuredatabricks.net".format(self.location),
                header,
                libraries,
                python_file,
                parameters,
                schedule,
                max_retries=max_retries,
                min_retry_interval_millis=min_retry_interval_millis,
                max_concurrent_runs=max_concurrent_runs
            )
            job_id = job.create_or_update(
                cluster_configs,
                parameters=parameters,
                schedule=schedule,
                python_file="dbfs:/batch_code/{}".format(os.path.basename(python_file)),
                max_concurrent_runs=max_concurrent_runs,
                max_retries=max_retries,
                min_retry_interval_millis=min_retry_interval_millis,
                email_notifications=email_notifications,
            )
            if snapshot_scheduler:
                self.snapshot_scheduler_jobs.append(f"{job_name}:{environment_variables['catalog_partitionkey']}")
            return job_id
        except Exception as e:
            logger.error(e)
            try:
                logger.error(e.response.text)
            except AttributeError:
                pass
            self.thread_exceptions.append(e)
            raise

    def deploy_batch_sources(self, databricks_token, batch_file_sources):
        """
        Deploy all the batch sources associated with an application.
        """
        func_config = []
        func_path = "{}/batchfile_ingestion/build/trigger".format(
            self.shared_functions_base_path
        )
        func_config_path = "{}/config.json".format(func_path)
        for source in batch_file_sources:
            # We need to grab the info for each source and added to the config. The
            # single config is written to the trigger function.
            source_name = source["name"]
            source_info = source["info"]
            transformations = source["properties"].get("transformations", [])
            source_file_path = source["properties"]["source_file_path"]
            func_config.append(
                {
                    "name": source_name,
                    "info": source_info,
                    "transformations": transformations,
                    "sourceFilePath": source_file_path,
                }
            )

        # Then create the config file, which has the source info for all sources.
        with open(func_config_path, "w") as f:
            f.write(json.dumps(func_config))

        self.deploy_batchfile_transformation(databricks_token)

    def deploy_batch_jobs(
        self,
        databricks_token: str,
        workspace: str,
        app_client_id: str = None,
        app_client_secret: str = None,
        batch_file_sources=[],
        batch_jobs=[],
        alerting=None,
    ):
        """
        Deploy all jobs in the application's batch folder as Databricks jobs.

        Args:
        """
        logger.info("Creating Databricks secret scope.")
        header = {"Authorization": "Bearer {}".format(databricks_token)}
        secret_client = DatabricksSecretClient(
            "https://{}.azuredatabricks.net".format(self.location), header
        )
        secret_scope = "udp-infra"
        secret_client.create_scope(secret_scope)
        secret_client.set_secret(secret_scope, "environment", self.environment)
        secret_client.set_secret(
            secret_scope, "datalakeaccount", self.lake_account_name
        )
        secret_client.set_secret(secret_scope, "datalakekey", self.lake_account_key)
        secret_client.set_secret(
            secret_scope, "appstorageaccount", self.app_storage_name
        )
        secret_client.set_secret(secret_scope, "appstoragekey", self.app_storage_key)
        udp_send_grid_key = self.kv_client.get_secret(
            "https://{key_vault_name}.vault.azure.net".format(
                key_vault_name=self.key_vault
            ),
            "UDP-SendGrid",
            "",
        ).value
        secret_client.set_secret(secret_scope, "udpsendgridkey", udp_send_grid_key)
        secret_client.set_secret(secret_scope, "databrickstoken", databricks_token)
        if app_client_id:
            secret_client.set_secret(secret_scope, "appclientid", app_client_id)
        if app_client_secret:
            secret_client.set_secret(secret_scope, "appclientsecret", app_client_secret)
        secret_client.set_secret(secret_scope, "tenantid", self.tenant)
        secret_client.set_secret(
            secret_scope,
            "keyvaulturl",
            "https://{key_vault_name}.vault.azure.net/".format(
                key_vault_name=self.azure_key_vault
            )
        )

        # Deploy event hub namespace listen-key connection string secrets
        for namespace in self.event_hub_namespaces:
            secret_client.set_secret(
                secret_scope,
                "{}-{}".format(namespace["namespace"], "listenkey"),
                namespace["listen_key"],
            )

        if self.sql_flag:
            secret_client.set_secret(secret_scope, "sqldbserver", self.real_time_server)
            # Only adding SQL Database secret if there's only one database.
            if len(self.sql_databases) == 1:
                secret_client.set_secret(
                    secret_scope, "sqldbdatabase", self.real_time_database
                )
            secret_client.set_secret(secret_scope, "sqldbuser", self.real_time_user)
            secret_client.set_secret(
                secret_scope, "sqldbpassword", self.real_time_password
            )

        if self.search_flag:
            search_key = self.kv_client.get_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault
                ),
                "search-admin-key",
                "",
            ).value
            search_query_key = self.kv_client.get_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.azure_key_vault
                ),
                "search-ro-key",
                "",
            ).value
            secret_client.set_secret(secret_scope, "searchname", self.search_name)
            secret_client.set_secret(secret_scope, "searchadminkey", search_key)
            secret_client.set_secret(secret_scope, "searchquerykey", search_query_key)

        libraries_required = [
            {"pypi": {"package": "azure-cosmosdb-table==1.0.6"}},
            {"pypi": {"package": "azure-storage-queue==12.1.2"}},
            {
                "maven": {
                    "coordinates": "com.microsoft.azure:azure-cosmosdb-spark_2.4.0_2.11:1.4.1"
                }
            },
        ]

        # Installing udp-utils to the job.
        self.deploy_databricks_library(
            databricks_token, workspace, "dbfs:/lib/", wheel_path=self.udp_utils_path
        )

        if self.libraries:
            libraries_required.extend(self.libraries)
        dbfs_libs = [
            list(p.values())[0]
            for p in libraries_required
            if "whl" in p or "egg" in p or "jar" in p
        ]
        for dbfs_lib in dbfs_libs:
            logger.info("Deploying library: {}".format(str(dbfs_lib)))
            self.deploy_databricks_library(
                databricks_token, workspace=workspace, dbfs_lib_path=dbfs_lib
            )

        # Adding udp-utils library to list. It's excluded previously because it's
        # in a separate folder and the loop above would fail.
        libraries_required.append(
            {"whl": "dbfs:/lib/{}".format(os.path.basename(self.udp_utils_path))}
        )
        base_env_variables = {"PYSPARK_PYTHON": "/databricks/python3/bin/python3"}
        source_batchfile_threads = []
        if alerting:
            email_notifications = {"no_alert_for_skipped_runs": True}
            if alerting.get("failure_emails"):
                email_notifications["on_failure"] = alerting.get("failure_emails")
            if alerting.get("success_emails"):
                email_notifications["on_success"] = alerting.get("success_emails")
        else:
            email_notifications = None
        if self.cosmos_url:
            secret_client.set_secret(secret_scope, "cosmosDBURL", self.cosmos_url)
            secret_client.set_secret(secret_scope, "cosmosDBKey", self.cosmos_key)

        # We'll deploy these in parallel since they have no dependency
        job_deploy_threads = []
        fs_client = DatabricksFS(
            "https://{}.azuredatabricks.net".format(self.location), header
        )
        fs_client.mkdirs("dbfs:/batch_code/")

        configJobs = (
            []
        )  # placeholder list to make sure these aren't run more than intended
        configJobNames = []  # placeholder list for complete list of job names
        batchPathJobs = []  # placeholder list for job names under batch file path.
        for job in batch_jobs:
            # create list of jobs
            configJobs.append(job["jobFile"])
            configJobNames.append(job["jobName"])
            # placeholder for schedule information
            schedule = {}
            # placeholder for job args
            job_args = []
            # placeholder for user-defined cluster config options
            cluster_user_config = {}
            max_retries = job.get("max_retries")
            min_retry_interval_millis = job.get("min_retry_interval_millis")
            max_concurrent_runs = job.get("max_concurrent_runs")
            # logic to get schedule information
            for (k, v) in job.items():
                if k == "schedule":
                    schedule["quartz_cron_expression"] = v.get("cron_expression")
                    schedule["timezone_id"] = v.get("timezone")
                # logic to get arguments
                elif k == "arguments":
                    job_args = v
                elif k == "autoscaleSettings":
                    cluster_user_config["autoscale_min_workers"] = v.get("min_workers")
                    cluster_user_config["autoscale_max_workers"] = v.get("max_workers")
                elif k == "numWorkers":
                    cluster_user_config["num_workers"] = v
                elif k == "nodeTypeId":
                    cluster_user_config["node_type_id"] = v
                elif k == "runtimeVersion":
                    cluster_user_config["spark_version"] = v
            thread = threading.Thread(
                target=self.deploy_databricks_job,
                args=(
                    fs_client,
                    databricks_token,
                    workspace,
                    job["jobName"],
                    os.path.join(self.batch_path, job["jobFile"]),
                ),
                kwargs={
                    "libraries": libraries_required,
                    "parameters": job_args,
                    "environment_variables": base_env_variables,
                    "max_retries": max_retries,
                    "min_retry_interval_millis" : min_retry_interval_millis,
                    "max_concurrent_runs": max_concurrent_runs,
                    "email_notifications": email_notifications,
                    "schedule": schedule,
                    "cluster_user_config": cluster_user_config,
                },
            )
            job_deploy_threads.append(thread)
            thread.start()

        # loop through all files under batch folder and add those files that are not already collected form config
        for r, d, f in os.walk(self.batch_path):
            for file in f:
                if file not in configJobs and file.endswith(".py"):
                    batchPathJobs.append(file.split(".")[0])
                    thread = threading.Thread(
                        target=self.deploy_databricks_job,
                        args=(
                            fs_client,
                            databricks_token,
                            workspace,
                            file.split(".")[0],
                            os.path.join(r, file),
                        ),
                        kwargs={
                            "libraries": libraries_required,
                            "environment_variables": base_env_variables,
                            "email_notifications": email_notifications,
                            "max_concurrent_runs": defaults.MAX_CONCURRENT_RUNS,
                        },
                    )
                    job_deploy_threads.append(thread)
                    thread.start()

        configJobNames += batchPathJobs

        snapshot_threads, snapshot_pathjobs, snapshot_scheduler = self.deploy_snapshot_load(
            fs_client,
            databricks_token,
            workspace,
            base_env_variables,
            email_notifications,
        )

        configJobNames += snapshot_pathjobs

        logger.info("Triggering cleanup of batch and snapshot")
        # Run cleanup for job files that are removed from config or removed from batch.
        fs_client.cleanup(configJobNames)

        logger.info("Waiting for all Databricks job deployment threads to finish.")
        for thread in job_deploy_threads:
            thread.join()
        for thread in snapshot_threads:
            thread.join()

        return snapshot_scheduler

        #Add Permission to jobs
        jobs = DatabricksJob()
        jobs.add_grants

    def deploy_snapshot_load(
        self,
        fs_client,
        databricks_token,
        workspace,
        base_env_variables,
        email_notifications,
    ):
        snapshot_threads = []
        snapshot_pathjobs = []
        # Only adding the UDP utils library. Should be all that's needed.
        libraries_required = {
            "whl": "dbfs:/lib/{}".format(os.path.basename(self.udp_utils_path))
        }

        # Need a flag to determine if the batchfile Function needs to be deployed.
        deploy_batchfile_app = False
        for source in self.source_list:
            if source["type"] != "udp":
                source_info = source["info"]

                # Deploying Databricks transformation job for processing layer.
                env_variables = base_env_variables.copy()
                landing_string_partition_key = "{}-{}".format(self.app_name, source["name"])
                deprecated_snapshot: bool = False
                if "processing" in source["properties"] or (
                    source["type"] == "db"
                    and "processing" in source["properties"]["tableInfo"]
                ):
                    deprecated_snapshot: bool = True
                    logger.warning(
                        'The "processing" config keyword is deprecated.  Please use "snapshot" instead.'
                    )
                if (
                    deprecated_snapshot
                    or "snapshot" in source["properties"]
                    or (
                        source["type"] == "db"
                        and "snapshot" in source["properties"]["tableInfo"]
                    )
                ):
                    snapshot_name = source["name"]
                    logger.info(f"Deploying snapshot utility for {snapshot_name}.")

                    # Loading into table UDPSnapshot
                    snapshot_table_entity = {
                        "PartitionKey": self.app_name,
                        "RowKey": source["name"],
                        "Description": source["info"]["description"],
                        "Region": source["info"]["region"],
                        "SecurityLevel": source["info"]["securityLevel"],
                        "SubjectArea": source["info"]["subjectArea"],
                        "Type": source["type"],
                    }

                    if deprecated_snapshot:
                        snapshot = source["properties"].get("processing") or source[
                            "properties"
                        ].get("tableInfo", dict()).get("processing")
                    elif source["type"] in ingestion_types:
                        source_class = ingestion_types[source["type"]]
                        source_instance = source_class(
                            self.app_name, source, self.shared_functions_base_path
                        )
                        snapshot = source_instance.get_source_snapshot_info()
                    else:
                        snapshot = source["properties"].get("snapshot") or source[
                            "properties"
                        ].get("tableInfo", dict()).get("snapshot")
                    load_type = snapshot.get("load_type", "type1")
                    # Convert `True` to `"true"` and `False` to `"false"`
                    drop_duplicates = json.dumps(snapshot.get("drop_duplicates", False))
                    # Only need to add to the transformations list if it's a batch source,
                    # otherwise it's triggered on a schedule.
                    load_utility_name = f"{snapshot_name}_load_utility".replace(
                        "-", "_"
                    ).lower()
                    snapshot_pathjobs.append(load_utility_name)
                    snapshot_scheduler = False
                    if source["type"] == "batchfile":
                        if load_type in ["type1"]:
                            # Just in case transformations weren't specified.
                            if source["properties"].get("transformations"):
                                source["properties"]["transformations"].append(
                                    load_utility_name
                                )
                            else:
                                source["properties"]["transformations"] = [
                                    load_utility_name
                                ]
                        job_schedule = None
                        env_variables["load_utility"] = snapshot.get(
                            "load_utility", snapshot.get("file_format", "csv")
                        )

                    else:
                        job_schedule = None
                        # If it's an event source use ndjson as the format.
                        env_variables["load_utility"] = snapshot.get(
                            "load_utility", snapshot.get("file_format", "ndjson")
                        )
                        snapshot_scheduler = True
                        deploy_batchfile_app = True

                    env_variables["catalog_partitionkey"] = landing_string_partition_key
                    env_variables["key_columns"] = ",".join(snapshot["key_columns"])
                    if snapshot.get("watermark"):
                        env_variables["watermark"] = ",".join(snapshot["watermark"])

                    env_variables["file_type"] = snapshot.get("batch_file_type", "delta")
                    env_variables["drop_duplicates"] = drop_duplicates
                    env_variables["load_type"] = load_type
                    env_variables["app_name"] = self.app_name
                    env_variables["source_name"] = snapshot_name
                    env_variables["source_region"] = source_info["region"]
                    env_variables["source_security_level"] = source_info["securityLevel"]
                    env_variables["source_subject_area"] = source_info["subjectArea"]
                    file_parameters = snapshot.get("file_parameters", dict())
                    # Environment variables must be str, and "-characters must be escaped.
                    # Databricks will consume quotes when loading the cluster environment variables.
                    env_variables["file_parameters"] = (
                        json.dumps(file_parameters)
                        .replace("\\", "\\\\")
                        .replace('"', '\\"')
                    )
                    # Set default spark version
                    cluster_user_config = {"spark_version": defaults.DBRICKS_SNAPHOT_RUNTIME}
                    # Override cluster config with snapshot settings, if provided
                    for key, val in snapshot.items():
                        if key == "autoscaleSettings":
                            cluster_user_config["autoscale_min_workers"] = val.get(
                                "min_workers"
                            )
                            cluster_user_config["autoscale_max_workers"] = val.get(
                                "max_workers"
                            )
                        elif key == "numWorkers":
                            cluster_user_config["num_workers"] = val
                        elif key == "nodeTypeId":
                            cluster_user_config["node_type_id"] = val

                    thread = threading.Thread(
                        target=self.deploy_databricks_job,
                        args=(
                            fs_client,
                            databricks_token,
                            workspace,
                            load_utility_name,
                            "{}/../../batch_utilities/delta_utility.py".format(
                                SCRIPT_DIRECTORY
                            ),
                        ),
                        kwargs={
                            "libraries": libraries_required,
                            "environment_variables": env_variables,
                            "max_concurrent_runs": 1,
                            "email_notifications": email_notifications,
                            "cluster_user_config": cluster_user_config,
                            "schedule": job_schedule,
                            "snapshot_scheduler": snapshot_scheduler,
                        },
                    )
                    snapshot_threads.append(thread)
                    thread.start()

                    self.table_service.create_table(self.snapshot_table_name)
                    self.table_service.insert_or_replace_entity(
                        self.snapshot_table_name, snapshot_table_entity
                    )

        return snapshot_threads, snapshot_pathjobs, deploy_batchfile_app

    def prep_sources(self):
        logger.info("Prepping data sources.")

        source_types: typing.Set[str] = set()

        region_source_list = [x for x in self.source_list if self.location in x.get("deployRegions", [defaults.LOCATION]) and x.get("enabled", True)]

        for source in region_source_list:
            source_type: str = source["type"]
            first: bool = source_type not in source_types
            source_types.add(source_type)

            # TODO The if statement guard can be removed once API and DB are moved into ingestion classes
            # The lines in the if block must stay though
            if source_type in ingestion_types:
                source_class = ingestion_types[source_type]
                source_instance = source_class(
                    self.app_name, source, self.shared_functions_base_path
                )
                source_instance.prep_source(
                    self.kv_client,
                    self.key_vault,
                    self.azure_key_vault,
                    self.table_service,
                    self.source_table_name,
                    first=first,
                )

            ######################################## START OF REMOVAL SECTION #########################################

            # The code below is here only to be kept until API and DB are moved into the ingestion classes

            source_name = source["name"]

            if source_type == "api":
                # Setting type flag for API source
                func_path = "{}/configurable_api_ingestion/build/{}".format(
                    self.shared_functions_base_path, source_name
                )
                if not os.path.exists(func_path):
                    os.mkdir(func_path)

                # Checking the auth type for API ingestion and getting required params.
                auth_type = source["properties"]["auth_type"]
                func_params = {}
                func_params["sourceName"] = source_name
                func_params["sourceUrl"] = source["properties"]["source_url"]
                func_params["authType"] = auth_type
                func_params["consumerKey"] = source["properties"].get(
                    "consumer_key", ""
                )
                func_params["clientId"] = source["properties"].get("client_id", "")
                func_params["secretKey"] = source["properties"].get("secret_key", "")
                func_params["tokenEndpoint"] = source["properties"].get(
                    "token_endpoint", ""
                )
                func_params["requestEndpoint"] = source["properties"].get(
                    "request_endpoint", ""
                )
                func_params["userAgent"] = source["properties"].get("user_agent", "")
                func_params["username"] = source["properties"].get("username", "")
                func_params["passwordSecret"] = source["properties"].get(
                    "password_secret_name", ""
                )
                func_params["itemKey"] = source["properties"].get("item_key", "")
                func_params["lengthKey"] = (
                    source["properties"].get("paging", {}).get("length_key", "")
                )
                func_params["length"] = (
                    source["properties"].get("paging", {}).get("length", "")
                )
                func_params["pageKey"] = (
                    source["properties"].get("paging", {}).get("page_key", "")
                )
                func_params["nextPageKey"] = (
                    source["properties"].get("paging", {}).get("next_page_key", "")
                )
                func_params["baseUrl"] = source["properties"].get("base_url", "")
                func_params["linkKey"] = source["properties"].get("link_key", "")
                func_params["urlParams"] = (
                    json.dumps(source["properties"].get("url_params", "{}"))
                    .replace("{", "{{")
                    .replace("}", "}}")
                    .replace('"', "'")
                    .replace("\\\\", "")
                )
                func_params["lastUpdateResponseKey"] = (
                    source["properties"]
                    .get("incremental", {})
                    .get("last_update_response_key", "")
                )
                func_params["lastUpdateParam"] = (
                    source["properties"]
                    .get("incremental", {})
                    .get("last_update_param", "")
                )
                func_params["eventHubNamespaceIndex"] = source["eventHubNamespaceIndex"]

                # Copying secrets to the app Key Vault.
                if func_params["passwordSecret"] != "":
                    # Allow App config templates  to specify a different source KV
                    kv = source["properties"].get("key_vault_name", self.key_vault)
                    secret = self.kv_client.get_secret(
                        f"https://{kv}.vault.azure.net",
                        func_params["passwordSecret"],
                        "",
                    ).value
                    self.kv_client.set_secret(
                        f"https://{self.azure_key_vault}.vault.azure.net",
                        func_params["passwordSecret"],
                        secret,
                    )
                func_json_path = "{}/function.json".format(func_path)
                with open(func_json_path, "w") as f:
                    bindings = [
                        {
                            "type": "timerTrigger",
                            "schedule": source["properties"]["schedule"],
                            "useMonitor": True,
                            "runOnStartup": False,
                            "name": "myTimer",
                        },
                        {
                            "type": "queue",
                            "direction": "out",
                            "name": "queueCollector",
                            "queueName": "api-trigger",
                            "connection": "AzureQueueStorage",
                        },
                    ]
                    bindings.extend(
                        [
                            {"type": "param", "name": key, "param": val}
                            for key, val in func_params.items()
                        ]
                    )
                    func_json = json.dumps(
                        {
                            "bindings": bindings,
                            "disabled": False,
                            "scriptFile": "../bin/api_ingestion.dll",
                            "entryPoint": "APIIngestion.ParseConfig.Run",
                        }
                    )
                    f.write(func_json)

            elif source_type == "db":
                # Setting type flag for DB source
                func_path = "{}/configurable_db_ingestion/build/{}".format(
                    self.shared_functions_base_path, source_name
                )
                if not os.path.exists(func_path):
                    os.mkdir(func_path)
                if source["properties"].get("dbConnectionTimeout"):
                    self.db_connection_timeout = source["properties"]["dbConnectionTimeout"]
                else:
                    self.db_connection_timeout = 30
                func_params = {}
                func_params["sourceName"] = source_name
                func_params["sourceDbType"] = source["properties"]["dbType"]
                func_params["sourceDbServer"] = source["properties"]["dbServer"]
                func_params["sourcePort"] = source["properties"]["portnumber"]
                func_params["sourceDbName"] = source["properties"]["dbName"]
                func_params["username"] = source["properties"]["username"]
                func_params["passwordSecret"] = source["properties"]["passwordSecret"]
                func_params["tableName"] = source["properties"]["tableInfo"][
                    "tableName"
                ]
                func_params["loadType"] = source["properties"]["tableInfo"]["loadType"]
                func_params["comparisonField"] = source["properties"]["tableInfo"].get(
                    "comparisonField", ""
                )
                func_params["refreshSchedule"] = source["properties"]["tableInfo"][
                    "refreshSchedule"
                ]
                func_params["eventHubNamespaceIndex"] = source["eventHubNamespaceIndex"]
                func_params["chunkRange"] = ""
                func_params["firstIngestFlag"] = ""

                # Copying secrets to the app Key Vault.
                if func_params["passwordSecret"] != "":
                    secret = self.kv_client.get_secret(
                        "https://{key_vault_name}.vault.azure.net".format(
                            key_vault_name=self.key_vault_db
                        ),
                        func_params["passwordSecret"],
                        "",
                    ).value
                    self.kv_client.set_secret(
                        "https://{key_vault_name}.vault.azure.net".format(
                            key_vault_name=self.azure_key_vault
                        ),
                        func_params["passwordSecret"],
                        secret,
                    )
                func_json_path = "{}/function.json".format(func_path)

                with open(func_json_path, "w") as f:
                    bindings = [
                        {
                            "type": "timerTrigger",
                            "schedule": source["properties"]["tableInfo"][
                                "refreshSchedule"
                            ],
                            "useMonitor": True,
                            "runOnStartup": False,
                            "name": "myTimer",
                        },
                        {
                            "type": "queue",
                            "direction": "out",
                            "name": "queueCollector",
                            "queueName": "db-ingestion",
                            "connection": "AzureQueueStorage",
                        },
                        {
                            "type": "table",
                            "direction": "in",
                            "name": "checkpointTable",
                            "tableName": "CheckpointTable",
                            "connection": "AzureWebJobsStorage",
                        },
                    ]
                    bindings.extend(
                        [
                            {"type": "param", "name": key, "param": val}
                            for key, val in func_params.items()
                        ]
                    )
                    func_json = json.dumps(
                        {
                            "bindings": bindings,
                            "disabled": False,
                            "scriptFile": "../bin/db_ingestion.dll",
                            "entryPoint": "DBIngestion.DetailsToQueue.Run",
                        }
                    )
                    f.write(func_json)

            ######################################## END OF REMOVAL SECTION #########################################

            # Setting up the data lake load function
            if source.get("eventHubNamespaceName"):
                dll_path = "{}/data_lake_load/build/{}".format(
                    self.shared_functions_base_path, source["name"]
                )
                if not os.path.exists(dll_path):
                    os.mkdir(dll_path)
                dll_json_path = "{}/function.json".format(dll_path)

                with open(dll_json_path, "w") as f:
                    bindings = [
                        {
                            "type": "eventHubTrigger",
                            "connection": "EventHub{}Connection".format(
                                source["eventHubNamespaceIndex"]
                            ),
                            "consumerGroup": "datalakeload",
                            "eventHubName": source["eventHub"].lower(),
                            "name": "eventHubMessageList",
                        },
                        {
                            "type": "queue",
                            "queueName": "data-lake-catalog-trigger",
                            "direction": "out",
                            "connection": "DataLakeAccountConnectionString",
                            "name": "queueCollector",
                        },
                        {
                            "type": "param",
                            "name": "sourceName",
                            "param": source["name"],
                        },
                        {
                            "type": "param",
                            "name": "sourceRegion",
                            "param": source["info"]["region"],
                        },
                        {
                            "type": "param",
                            "name": "sourceSecurityLevel",
                            "param": source["info"]["securityLevel"],
                        },
                        {
                            "type": "param",
                            "name": "sourceSubjectArea",
                            "param": source["info"]["subjectArea"],
                        },
                    ]
                    func_json = json.dumps(
                        {
                            "bindings": bindings,
                            "disabled": False,
                            "scriptFile": "../bin/data_lake_load.dll",
                            "entryPoint": "LoadFunctions.DataLakeLoad.Run",
                        }
                    )
                    f.write(func_json)

        # Remove reference functions
        for source in source_types:
            # TODO This if statement guard can be removed once API and DB are in ingestion classes
            # The lines in the if block must stay though
            if source in ingestion_types:
                ingestion_types[source].clean_build_path(
                    self.shared_functions_base_path
                )

        return source_types

    def deploy_sources(self):

        thread = threading.Thread(
            target=self._deploy_sources,
        )

        thread.start()
        self.source_threads.append(thread)

    def _deploy_sources(self):
        t = time.time()
        try:
            logger.info("Starting source deployment.")
            networking = {}
            sources = self.prep_sources()
            self.source_threads = []

            # map for current application
            networking_App = defaults.asp_vnet_injection_map.get(self.app_name)

            if networking_App and self.environment in defaults.ENVS:
                networking = networking_App[self.location].get(self.environment)

            for source in sources:
                if source in ingestion_types:
                    thread = threading.Thread(target=self.deploy_ingestion_function, args= [source])
                    self.source_threads.append(thread)
                    thread.start()

                if source == "api":
                    thread = threading.Thread(target=self.deploy_api_ingestion)
                    self.source_threads.append(thread)
                    thread.start()

                if source == "db":
                    thread = threading.Thread(target=self.deploy_db_ingestion, args=[networking])
                    self.source_threads.append(thread)
                    thread.start()

            for threads in self.source_threads:
                threads.join()

            self.deploy_dll()

        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def deploy_real_time(
        self, consumer_groups: list, runtime: str, hostingPlan=None, custom_secrets=None
    ):
        self.wait_batch()
        thread = threading.Thread(
            target=self._deploy_real_time,
            args=(consumer_groups, runtime, hostingPlan, custom_secrets),
        )
        thread.start()
        self.threads.append(thread)

    def _deploy_real_time(
        self, consumer_groups: list, runtime: str, hostingPlan=None, custom_secrets=None,
    ):
        t = time.time()
        try:
            app_settings = {}
            networking = {}
            logger.info(
                "Deploying RealTimeLayer for app {} in {}.".format(self.app_name, self.environment)
            )

            # map for current application
            networking_App = defaults.asp_vnet_injection_map.get(self.app_name)

            if networking_App and self.environment in defaults.ENVS:
                networking = networking_App[self.location].get(self.environment)

            # Adding UDP Send grid key vault secret to jll-cus-fa-udp-test-rt-dev function app
            udp_send_grid_id = self.kv_client.get_secret(
                "https://{key_vault_name}.vault.azure.net".format(
                    key_vault_name=self.key_vault
                ),
                "UDP-SendGrid",
                "",
            ).value
            app_settings["AzureWebJobsSendGridApiKey"] = udp_send_grid_id

            if hostingPlan == "appserviceplan" and runtime != "dotnet":
                app_settings["FUNCTIONS_WORKER_PROCESS_COUNT"] = 10

            if custom_secrets:
                for secret in custom_secrets:
                    secret_value = self.kv_client.get_secret(
                        "https://{key_vault_name}.vault.azure.net".format(
                            key_vault_name=self.key_vault
                        ),
                        secret["name"],
                        "",
                    ).value
                    if secret_value:
                        appsettingsName = (
                            secret["appSettingName"]
                            if "appSettingName" in secret
                            else secret["name"]
                        )
                        app_settings[appsettingsName] = secret_value

            consumer_group_regions = [x for x in consumer_groups if self.location in x.get("deployRegions", [defaults.LOCATION])]

            for consumer_group in consumer_group_regions:
                # Get the source record from the sources table.
                # This helps to support shared sources, as well as partial deployments
                # during development.
                try:
                    source_entry = self.table_service.get_entity(
                        self.source_table_name,
                        self.app_name,
                        consumer_group["sourceName"],
                    )
                except AzureMissingResourceHttpError as e:
                    logger.error(
                        "Failed to find source {} when deploying consumer groups during real-time deployment.".format(
                            consumer_group["sourceName"]
                        )
                    )
                    self.thread_exceptions.append(e)
                    raise e

                resource_group = source_entry.EventHubResourceGroup
                namespace = source_entry.EventHubNamespace
                self.deploy_consumer_group(
                    source_entry.EventHub,
                    consumer_group["consumerGroupName"],
                    resource_group=resource_group,
                    namespace=namespace,
                )
                # For ease of use in the bindings, we add an AppSetting for each source.
                # We also add an AppSetting for each Event Hub name to abstract it
                # from the end user.

                if source_entry.Type == "shared":
                    # If it's a shared source, we get the key from the Event Hub.
                    rule_keys = self.eh_client.event_hubs.list_keys(
                        source_entry.EventHubResourceGroup,
                        source_entry.EventHubNamespace,
                        source_entry.EventHub,
                        "shared-{}".format(self.app_name),
                    )
                    connection = rule_keys.primary_connection_string

                else:
                    # Otherwise grab the listen conn from the namespace.
                    rule_keys = self.eh_client.namespaces.list_keys(
                        source_entry.EventHubResourceGroup,
                        source_entry.EventHubNamespace,
                        "listen-key".format(source_entry.EventHubNamespace),
                    )
                    connection = rule_keys.primary_connection_string

                app_settings[consumer_group["sourceName"] + "-connection"] = connection
                app_settings[
                    consumer_group["sourceName"] + "-eventhub"
                ] = source_entry.EventHub

            if runtime == "python" or runtime == "java":
                # Azure has a limitation where special characters are not
                # allowed in AppSetting names in a Linux environment
                app_settings = {
                    re.sub("[^A-Za-z0-9]+", "_", key): value
                    for key, value in app_settings.items()
                }

            _ = self.deploy_function_app(
                "rt",
                self.real_time_path,
                "The real-time Function App. This App contains all real-time functions that were found in the real_time folder within the application repository.",
                runtime=runtime,
                hostingPlan=hostingPlan,
                networking=networking,
                app_settings=app_settings,
                singleAspFlag=self.singleAspFlag,
                use_blob=runtime == "python" or runtime == "java",
            )
            
            logger.info(
                "Real-time deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise

    def deploy_web_app(self, sku=None):
        self.wait_api()
        thread = threading.Thread(target=self._deploy_web_app, kwargs={"sku": sku})
        thread.start()
        self.threads.append(thread)

    def _deploy_web_app(self, sku=None):
        """
        Deploy an Azure Web App, optionally specifying a SKU (defaults to S1).
        """
        t = time.time()
        try:
            param_object = self.parameters_object.copy()
            param_object["location"] = {"value": self.location}
            param_object["regionCode"] = {"value": self.region_code}
            param_object["environment"] = {"value": self.compute_environment}
            param_object["windowsResourceGroupName"] = {
                "value": self.resource_group
            }
            param_object["keyVaultName"] = {"value": self.azure_key_vault}
            param_object["emailReceivers"] = {
                "value": json.dumps(self.email_receivers)
            }
            if sku:
                param_object["sku"] = {"value": sku}

            logger.info(f"Deploying Azure Web App for {self.app_name}.")
            outputs = self.deploy_resource_template(
                "web_app", param_object, resource_group=self.web_resource_group
            )
            web_app_name = outputs["webAppPortalName"]["value"]
            self.deploy_function(
                web_app_name,
                self.web_path,
                resource_group=self.web_resource_group
            )

            logger.info(
                "Web layer deployment finished successfully after {}.".format(
                    timedelta(seconds=(time.time() - t))
                )
            )
        except Exception as e:
            self.thread_exceptions.append(e)
            raise e

    def deploy_spa(self):
        thread = threading.Thread(target=self._deploy_spa, args=())
        thread.start()
        self.threads.append(thread)

    def _deploy_spa(self):
        logger.info("Creating storage account for single page app.")
        spa_blob = "{0}{1}saudp{2}spa{3}".format(
            self.org_name, self.region_code, self.app_name, self.environment
        )
        poller = self.storage_client.storage_accounts.create(
            resource_group_name=self.compute_resource_group,
            account_name=spa_blob,
            parameters=StorageAccountCreateParameters(
                sku=Sku(name="Standard_LRS"),
                kind="StorageV2",
                location=self.location,
                tags={
                    "AppName": self.parameters_object["projectInformation"]["value"][
                        "AppName"
                    ],
                    "AppOwner": self.parameters_object["projectInformation"]["value"][
                        "AppOwner"
                    ],
                    "BusLine": self.parameters_object["projectInformation"]["value"][
                        "BusLine"
                    ],
                    "CostCenter": self.parameters_object["projectInformation"]["value"][
                        "CostCenter"
                    ],
                    "Environment": self.parameters_object["projectInformation"][
                        "value"
                    ]["Environment"],
                    "TechOwner": self.parameters_object["projectInformation"]["value"][
                        "TechOwner"
                    ],
                    "OwnerEmail": self.parameters_object["projectInformation"]["value"][
                        "OwnerEmail"
                    ],
                    "Description": "The storage account for the single-page web application.",
                },
            ),
            polling=True,
        )
        poller.wait()
        storage_keys = self.storage_client.storage_accounts.list_keys(
            self.compute_resource_group, spa_blob
        )
        storage_keys = {v.key_name: v.value for v in storage_keys.keys}
        spa_key = storage_keys["key1"]

        logger.info(f"Setting up Storage Analytics logging on the {spa_blob} storage account.")
        # Creating BlobServiceClient
        blob_service_client = BlobServiceClient(account_url=f"https://{spa_blob}.blob.core.windows.net", credential=spa_key)
        static_website = StaticWebsite(enabled=True, index_document="index.html", error_document404_path="index.html")

        # Create logging settings
        logging = BlobAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))

        # Create metrics for requests statistics
        hour_minute_metrics = Metrics(enabled=True, include_apis=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        blob_service_client.set_service_properties(analytics_logging=logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics, static_website=static_website)

        # Getting current blobs to delete anything left over after deployment.
        container_client = blob_service_client.get_container_client("$web")
        existing_blobs = container_client.list_blobs()

        # Set Storage Analytics Properties for Tables in the SPA Storage Account
        spa_table_service = TableService(account_name=spa_blob, account_key=spa_key)
        table_logging = Logging(delete=True, read=True, write=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        spa_table_service.set_table_service_properties(logging=table_logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        # Set Storage Analytics Properties for Queues in the SPA Storage Account
        queue_service_client = QueueServiceClient(account_url=f"https://{spa_blob}.queue.core.windows.net/", credential=spa_key)
        queue_logging = QueueAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        queue_service_client.set_service_properties(analytics_logging=queue_logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        web_build_path = self.web_path + "/build"
        rootdir = Path(web_build_path)

        # Getting environment variables for replacement.
        if self.environment in ["dev", "uat", "prd"]:
            env_fpath = Path(self.config_path + f"/{self.environment}.env.replace")
            logger.info(
                f"Found environment file {env_fpath} for SPA. Replacing variables."
            )
        else:
            env_fpath = Path(self.config_path + "/sbx.env.replace")
            logger.info(f"No environment file found for SPA variable replacement.")

        config = ConfigParser()
        config.optionxform = str
        default_config = config["DEFAULT"]

        if env_fpath.is_file():
            with open(env_fpath, "r") as f:
                f_content = f.read()
            config.read_string(f_content)
            default_config = config["DEFAULT"]

        # Loop through each of the web files, replace variables, and upload.
        logger.info("Deploying web application files to blob storage.")
        web_files = rootdir.glob("**/*")
        web_file_paths = []
        for f in web_files:
            if f.is_file():

                file_path = Path(f)
                relative_path = file_path.relative_to(web_build_path)
                blob_client = blob_service_client.get_blob_client(container="$web", blob=str(relative_path))
                web_file_paths.append(re.sub(r"\\+", "/", str(relative_path)))
                content_type = mimetypes.types_map.get(
                    relative_path.suffix, "text/html"
                )
                if relative_path.suffix in [".js", ".map"]:
                    with open(f, "r", encoding="latin-1") as file_obj:
                        file_content = file_obj.read()
                        for key in default_config:
                            val = default_config[key]
                            file_content = file_content.replace(
                                "$({})".format(key), val
                            )

                        blob_client.upload_blob(data=file_content, overwrite=True, content_settings=ContentSettings(content_type=content_type), encoding="latin-1")
                else:
                    with open(f, "rb") as data:
                        blob_client.upload_blob(data=data, overwrite=True, content_settings=ContentSettings(content_type=content_type))

        # Loop through existing blobs and delete if they weren't in web folder.
        logger.info("Deleting any existing files from web container.")
        for f in existing_blobs:
            if f.name not in web_file_paths:
                container_client.delete_blob(blob=f.name)

    def pre_deploy_cleanup(self):
        """
        Any pre-deploy clean-up activities for legacy/unused resources can go here.
        All methods here should be written to no-op if the resource has already
        been deleted.
        """
        old_salesforce_ing = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-salesforceing-{self.environment}"
        logger.info(
            f"Deleting old Salesforce ingestion {old_salesforce_ing} if it exists."
        )
        self.client.resources.delete(
            self.web_resource_group, "Microsoft.Web", "", "sites", old_salesforce_ing, "2016-08-01",
        ).result()
        old_salesforce_asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-salesforceing-{self.environment}"
        logger.info(
            f"Deleting old Salesforce ASP {old_salesforce_asp} if it exists."
        )
        self.client.resources.delete(
            self.web_resource_group, "Microsoft.Web", "", "serverfarms", old_salesforce_asp, "2019-08-01",
        ).result()

        old_rca_ing = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-rcaing-{self.environment}"
        logger.info(
            f"Deleting old RCA ingestion {old_rca_ing} if it exists."
        )
        self.client.resources.delete(
            self.web_resource_group, "Microsoft.Web", "", "sites", old_rca_ing, "2016-08-01"
        ).result()
        old_rca_asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-rcaing-{self.environment}"
        logger.info(
            f"Deleting old RCA ASP {old_rca_asp} if it exists."
        )
        self.client.resources.delete(
            self.web_resource_group, "Microsoft.Web", "", "serverfarms", old_rca_asp, "2019-08-01",
        ).result()

        old_box_ing = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-boxing-{self.environment}"
        logger.info(
            f"Deleting old Box ingestion {old_box_ing} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "sites", old_box_ing, "2016-08-01"
        ).result()
        old_box_asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-boxing-{self.environment}"
        logger.info(
            f"Deleting old Box ASP {old_box_asp} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "serverfarms", old_box_asp, "2019-08-01",
        ).result()

        old_ftp_ing = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-ftping-{self.environment}"
        logger.info(
            f"Deleting old FTP ingestion {old_ftp_ing} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "sites", old_ftp_ing, "2016-08-01",
        ).result()
        old_ftp_asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-ftping-{self.environment}"
        logger.info(
            f"Deleting old FTP ASP {old_ftp_asp} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "serverfarms", old_ftp_asp, "2019-08-01",
        ).result()

        old_reonomy_ing = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-reonomying-{self.environment}"
        logger.info(
            f"Deleting old Reonomy ingestion {old_reonomy_ing} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "sites", old_reonomy_ing, "2016-08-01",
        ).result()
        old_reonomy_asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-reonomying-{self.environment}"
        logger.info(
            f"Deleting old Reonomy ASP {old_reonomy_asp} if it exists."
        )
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "serverfarms", old_reonomy_asp, "2019-08-01",
        ).result()

        # Delete old autoscale name
        old_autoscale = f"{self.org_name}-{self.region_code}-fad-udp-{self.app_name}-bxfm-{self.environment}-autoscale"
        logger.info(
            f"Deleting old Autoscale {old_autoscale} if it exists."
        )
        self.client.resources.delete(
            self.web_resource_group, "Microsoft.insights", "", "autoscalesettings", old_autoscale, "2015-04-01",
        ).result()

        #Set KeyVault SoftDelete for existing keyvaults
        app_keyvault = f"{self.org_name}-{self.region_code}-kv-{self.app_name}-{self.environment}"
        logger.info(
            f"Enabling soft-delete in keyvault - {app_keyvault} - {self.azure_key_vault_new_or_existing}"
        )
        if(self.azure_key_vault_new_or_existing == "existing"):
            vault_prop = {'enable_soft_delete': True, 'soft_delete_retention_in_days': defaults.KV_Retention_Days}
            self.kv_mgmt_client.vaults.update(resource_group_name = self.resource_group, vault_name = app_keyvault, properties = vault_prop)
        

    def post_deploy_cleanup(self):
        """
        Any post-deploy clean-up activities for legacy/unused resources can go here.
        All methods here should be written to no-op if the resource has already
        been deleted.
        """
        # TODO: uncomment once VNET integration is working
        # old_batch_workspace = f"{self.org_name}-{self.region_code}-dbr-udp-batch-{self.app_name}-{self.environment}"
        # logger.info(f"Deleting old batch workspace {old_batch_workspace} if it exists.")
        # self.client.resources.delete(
        #     self.resource_group,
        #     "Microsoft.Databricks",
        #     "",
        #     "workspaces",
        #     old_batch_workspace,
        #     "2018-04-01",
        # ).wait()

        resources = ["rt","dbing"]
        if self.singleAspFlag :
            #clean up consumption plans
            logger.info(f"Deleting consumption plans if it exists.")

            for res in resources:
                app = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-{res}-{self.environment}"
                asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-{res}-{self.environment}"
                logger.info(f"app-{app}")
                logger.info(f"asp-{asp}")

                self.client.resources.delete(
                    self.resource_group,
                    "Microsoft.Web",
                    "",
                    "sites",
                    app,
                    "2016-08-01",
                ).wait()
                self.client.resources.delete(
                    self.resource_group,
                    "Microsoft.Web",
                    "",
                    "serverfarms",
                    asp,
                    "2016-09-01",
                ).wait()

        else:
            #clean up app service plans
            logger.info(f"Deleting appservice plans if it exists.")

            for res in resources:
                app = f"{self.org_name}-{self.region_code}-fad-udp-{self.app_name}-{res}-{self.environment}"
                logger.info(f"app-{app}")
                self.client.resources.delete(
                    self.resource_group,
                    "Microsoft.Web",
                    "",
                    "sites",
                    app,
                    "2016-08-01",
                ).wait()

            asp = f"{self.org_name}-{self.region_code}-asp-udp-{self.app_name}-win-{self.environment}"
            logger.info(f"asp-{asp}")
            self.client.resources.delete(
                    self.resource_group,
                    "Microsoft.Web",
                    "",
                    "serverfarms",
                    asp,
                    "2016-09-01",
            ).wait()

        eu2_batch_workspace = f"{self.org_name}-eu2-dbr-udp-batch-{self.app_name}-{self.environment}"
        logger.info(f"Deleting old EU2 batch workspace {eu2_batch_workspace} if it exists.")
        self.client.resources.delete(
            self.resource_group,
            "Microsoft.Databricks",
            "",
            "workspaces",
            eu2_batch_workspace,
            "2018-04-01",
        ).wait()

        old_bxfm_fa = f"{self.org_name}-{self.region_code}-fa-udp-{self.app_name}-bxfm-{self.environment}"
        logger.info(f"Deleting old batch transformation {old_bxfm_fa} if it exists.")
        self.client.resources.delete(
            self.resource_group, "Microsoft.Web", "", "sites", old_bxfm_fa, "2016-08-01"
        ).result()

    def wait_other(self):
        """
        Wait for other threads to complete before returning.
        """
        logger.info("Waiting for other threads to return")
        for thread in self.threads:
            thread.join()
        logger.info("All threads returned.")

    def wait_key_vault(self):
        """
        Wait for key_vault deployment to finish.
        """
        logger.info("Waiting for key_vault deployment to finish.")
        for thread in self.key_vault_threads:
            thread.join()
        logger.info("All key_vault threads returned.")

    def wait_namespace(self):
        """
        Wait for all namespace deployments to finish.
        """
        logger.info("Waiting for namespace deployments to finish.")
        for thread in self.namespace_threads:
            thread.join()
        logger.info("All namespace threads returned.")

    def wait_data_store(self):
        """
        Wait for all data store deployments to finish.
        """
        logger.info("Waiting for data store deployments to finish.")
        for thread in self.data_store_threads:
            thread.join()
        logger.info("All data store threads returned.")

    def wait_sources(self):
        """
        Wait for all source deployments to finish.
        """
        logger.info("Waiting for source deployments to finish.")
        for thread in self.source_threads:
            thread.join()
        logger.info("All source threads returned.")

    def wait_api(self):
        """
        Wait for all API deployments to finish.
        """
        logger.info("Waiting for API deployments to finish.")
        for thread in self.api_threads:
            thread.join()
        logger.info("All API threads returned.")

    def wait_batch(self):
        """
        Wait for all Databricks Batch Workspace deployments to finish.
        """
        logger.info("Waiting for Databricks Batch Workspace deployments to finish.")
        for thread in self.batch_threads:
            thread.join()
        logger.info("All Databricks Batch Workspace threads returned.")

    def wait_all(self):
        threads = self.threads
        threads.extend(self.namespace_threads)
        threads.extend(self.data_store_threads)
        threads.extend(self.source_threads)
        threads.extend(self.api_threads)
        threads.extend(self.batch_threads)
        logger.info(f"Waiting for all {self.location} deployments to finish.")
        for thread in threads:
            thread.join()
        if len(self.thread_exceptions) > 0:
            logger.error(f"All {self.location} threads completed, but there were errors.")
            raise Exception("Thread(s) completed with errors.")
        else:
            logger.info(f"All {self.location} threads returned successfully.")


def deploy_main_arm_template(
    app_only, validate_only, octopusvariables, env, resource_group, org_name, location, alerting
):
    """
    Deploy the main ARM template if the script is not running in validate only mode and one of the
    following conditions is met: 1) the script is not running on Octopus
                                 2) the Octopus environment is Sandbox
                                 3) the Octopus tenant is UDPCore

    Args:
        app_only: Boolean indicating that this should be skipped
        validate_only: Boolean indicating if the script is running in validate only mode
        octopusvariables: Dictionary of Octopus environment variables
        env: The name of the environment being deployed to
        resource_group: The name of the resource group being deployed to
        org_name: The name of the organization that owns the app being deployed

    Returns:
        Boolean indicating if the main ARM template was deployed
    """
    if (
        not validate_only
        and not app_only
        and (
            not octopusvariables
            or octopusvariables["Octopus.Environment.Name"] == "Sandbox"
            or octopusvariables["Octopus.Deployment.Tenant.Name"] == "UDPCore"
        )
    ):
        logger.info("Deploying main template to: " + location)

        main_deployer = ResourceDeployer(
            env, resource_group, org_name, "udp", octopusvariables=octopusvariables, location=location, alerting=alerting
        )
        param_object = main_deployer.parameters_object.copy()
        # param_object["location"] = {"value": location}

        if "projectInformation" in param_object:
            del param_object["projectInformation"]

        # TODO: Hardcoding the environment for eCRM replication for now. This will
        # need to be updated.
        if (main_deployer.environment == "dev" and location in defaults.PRIMARY_LOCATIONS):

            logger.info("Deploying eCrm Replication in : "+ location)
            ecrm_account_key = main_deployer.kv_client.get_secret(
                f"https://{main_deployer.key_vault}.vault.azure.net",
                f"udpecrmaccountkey{main_deployer.key_vault_env}",
                "",
            ).value
            param_object["eCRMAccountKey"] = {"value": ecrm_account_key}
            # Stopping eCRM replication trigger before deploying. ADF triggers can't be
            # running during deployment.
            run_history = False
            adf_name = "-".join([
                main_deployer.org_name,
                main_deployer.region_code,
                "adf",
                "udp",
                main_deployer.environment
            ])
            try:
                main_deployer.adf_client.triggers.stop(
                    main_deployer.resource_group,
                    adf_name,
                    "eCRMReplicateTrigger"
                )
            except CloudError as e:
                # Check the inner exception to see if the resource doesn't exist yet.
                if e.inner_exception.error == "ResourceNotFound":
                    logger.warn("ADF not yet deployed. Cannot disable trigger.")
                    # If it doesn't exist we'll have to catch up history.
                    run_history = True
                else:
                    raise e
        else:
            param_object["eCRMAccountKey"] = {"value": "dummy"}

        param_object["networking"] = {"value": defaults.pe_vnet_injection_map}

        if main_deployer.email_receivers:
            param_object["emailReceivers"] = {"value": main_deployer.email_receivers}

        outputs = main_deployer.deploy_resource_template(
            "main", param_object
        )

        logger.info(f'Setting up Storage Analytics logging on the {outputs["storageAccountName"]["value"]} storage account.')
        # Creating the blob service client with the name and key. These were captured as
        # output of the application main ARM template.
        blob_service_client = BlobServiceClient(account_url=f'https://{outputs["storageAccountName"]["value"]}.blob.core.windows.net', credential=outputs["storageAccountKey"]["value"])
        # Create logging settings
        logging = BlobAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        # Create metrics for requests statistics
        hour_minute_metrics = Metrics(enabled=True, include_apis=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        blob_service_client.set_service_properties(analytics_logging=logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        # Set Storage Analytics Properties for Queues
        queue_service_client = QueueServiceClient(account_url=f'https://{outputs["storageAccountName"]["value"]}.queue.core.windows.net/', credential=outputs["storageAccountKey"]["value"])
        queue_logging = QueueAnalyticsLogging(version="2.0", read=True, write=True, delete=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        queue_service_client.set_service_properties(analytics_logging=queue_logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        logger.info("Creating filesystems and folders and setting up ACLs in lake.")
        adls_client = DataLakeGen2Client(
            outputs["storageAccountName"]["value"],
            outputs["storageAccountKey"]["value"],
        )
        adls_client.create_filesystem("raw")
        adls_client.create_filesystem("processed")
        adls_client.create_filesystem("snapshot")
        adls_client.create_filesystem("ecrm")

        permission_map = {
            "global": {
                "public": "b86cd267-bd27-464e-b13a-1ce5b4f85da3",
                "internal": "ba977ca4-369c-4a59-a989-c193c30f17bf",
                "restricted": "2ab2860b-21c0-4b2c-9e5a-586d155d265d",
                "confidential": "7f8c864f-8091-4927-bbd5-12ccc3ef286f",
            },
            "emea": {
                "public": "2f044d8f-b1af-441a-85d6-fe6c8b810358",
                "internal": "af231327-5dbf-40c8-ae7e-85c0bbd250b6",
                "restricted": "8238ffc9-78c4-46d8-a744-6008b57dcebc",
                "confidential": "57a408e4-bf36-46d0-99c3-1acc7a96dca1",
            },
            "apac": {
                "public": "7363ebcd-f0e6-41f6-b17b-affc5e6db072",
                "internal": "1870f806-d2f4-43d1-9bb4-07dbb8b2f4b2",
                "restricted": "5a9534ec-f57f-43b4-8b07-f6648f6b288b",
                "confidential": "74826ad1-c5a8-408d-a539-87425aaca196",
            },
            "amer": {
                "public": "5981673b-34f4-451d-986b-35755eb067fc",
                "internal": "f54b4f44-2557-4ffc-a670-18bc5e9615a9",
                "restricted": "f2b72c15-b922-4185-8a3d-44e2c71dc14c",
                "confidential": "cd66ed94-f51b-4a1a-99a3-30b479f9974b",
            },
        }
        restricted_subject_areas = [
            # Employee restricted group for HR data
            {
                "region": "global",
                "subjectArea": "employee",
                "roleGroup": "e98943f7-4724-45b3-ad4a-ba295e35e2e5",
            },
            {
                "region": "amer",
                "subjectArea": "employee",
                "roleGroup": "7d306edc-0689-4b8a-b7e3-d7ef3a5a69e2",
            },
            {
                "region": "apac",
                "subjectArea": "employee",
                "roleGroup": "28c6f6f0-c867-451c-b71e-f6240b0afe56",
            },
            {
                "region": "emea",
                "subjectArea": "employee",
                "roleGroup": "dcee4a52-ba5a-4b1f-a949-cccdd49ba158",
            },
            # Opportinity restricted group for opportunity and fee data
            {
                "region": "global",
                "subjectArea": "opportunity",
                "roleGroup": "229de334-a2d9-49f4-bcc0-88af62da3e43",
            },
            {
                "region": "amer",
                "subjectArea": "opportunity",
                "roleGroup": "d7de500d-8198-4c9b-a6cf-6fcb2c820a0e",
            },
            {
                "region": "apac",
                "subjectArea": "opportunity",
                "roleGroup": "03e1f773-1fad-45b0-b79c-de276bcc874a",
            },
            {
                "region": "emea",
                "subjectArea": "opportunity",
                "roleGroup": "b1f4fb25-3b56-4735-8825-6f205921c4f2",
            },
            {
                "region": "global",
                "subjectArea": "cs-employee",
                "roleGroup": "29cbe0ae-f748-4fb6-919e-83455beb2cd1",
            },
            {
                "region": "amer",
                "subjectArea": "cs-employee",
                "roleGroup": "3e3a1feb-56c2-40d5-8683-ebc500eddea6",
            },
            {
                "region": "apac",
                "subjectArea": "cs-employee",
                "roleGroup": "345fb7e6-a9f1-4885-8384-afe7765b6617",
            },
            {
                "region": "emea",
                "subjectArea": "cs-employee",
                "roleGroup": "b9bf584e-72e8-4b73-8811-a0ef6f37495a",
            },
        ]

        # First set up permissions for the eCRM filesystem.
        ecrm_acl = [
            f"default:group:{main_deployer.core_role_group}:r-x",
            f"group:{main_deployer.core_role_group}:r-x",
            "default:group:4ba58561-7cf2-4c0b-b4cc-7d8281f9b122:rwx",
            "group:4ba58561-7cf2-4c0b-b4cc-7d8281f9b122:rwx",
            f"default:group:{permission_map['amer']['internal']}:r-x",
            f"group:{permission_map['amer']['internal']}:r-x",
        ]
        adls_client.set_path_acl("ecrm", "/", new_acl=",".join(ecrm_acl))

        root_acl = [
            "default:group:{}:--x".format(main_deployer.core_role_group),
            "group:{}:r-x".format(main_deployer.core_role_group),
        ]
        for region, val in permission_map.items():
            region_acl = []
            for security_level, group in val.items():
                root_acl.append("default:group:{}:--x".format(group))
                root_acl.append("group:{}:r-x".format(group))
                region_acl.append("default:group:{}:--x".format(group))
                region_acl.append("group:{}:r-x".format(group))

                # create paths
                adls_client.create_path("raw", "/{}/{}/".format(region, security_level))
                adls_client.create_path(
                    "processed", "/{}/{}/".format(region, security_level)
                )
                adls_client.create_path(
                    "snapshot", "/{}/{}/".format(region, security_level)
                )

                # Setting the actual default permissions for the security level folders.
                adls_client.set_path_acl(
                    "raw",
                    "/{}/{}/".format(region, security_level),
                    new_acl="default:group:{0}:r-x,group:{0}:r-x".format(group),
                )
                adls_client.set_path_acl(
                    "processed",
                    "/{}/{}/".format(region, security_level),
                    new_acl="default:group:{0}:r-x,group:{0}:r-x".format(group),
                )
                adls_client.set_path_acl(
                    "snapshot",
                    "/{}/{}/".format(region, security_level),
                    new_acl="default:group:{0}:r-x,group:{0}:r-x".format(group),
                )

            # Setting executing permissions so that the users can access subfolders.
            adls_client.set_path_acl(
                "raw", "/{}/".format(region), new_acl=",".join(region_acl)
            )
            adls_client.set_path_acl(
                "processed", "/{}/".format(region), new_acl=",".join(region_acl)
            )
            adls_client.set_path_acl(
                "snapshot", "/{}/".format(region), new_acl=",".join(region_acl)
            )

        # Setup permissions for restricted subject areas
        for d in restricted_subject_areas:
            adls_client.create_path(
                "raw",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
            )
            adls_client.create_path(
                "processed",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
            )
            adls_client.create_path(
                "snapshot",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
            )

            # Setting the actual default permissions for the security level folders.
            adls_client.set_path_acl(
                "raw",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
                new_acl="default:group:{0}:r-x,group:{0}:r-x".format(d["roleGroup"]),
            )
            adls_client.set_path_acl(
                "processed",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
                new_acl="default:group:{0}:r-x,group:{0}:r-x".format(d["roleGroup"]),
            )
            adls_client.set_path_acl(
                "snapshot",
                "/{}/{}/{}/".format(d["region"], "confidential", d["subjectArea"]),
                new_acl="default:group:{0}:r-x,group:{0}:r-x".format(d["roleGroup"]),
            )

        adls_client.set_path_acl("raw", "/", new_acl=",".join(root_acl))
        adls_client.set_path_acl("processed", "/", new_acl=",".join(root_acl))
        adls_client.set_path_acl("snapshot", "/", new_acl=",".join(root_acl))

        main_deployer.table_service = TableService(
            account_name=outputs["storageAccountName"]["value"],
            account_key=outputs["storageAccountKey"]["value"],
        )

        # Set Storage Analytics Properties for Tables
        logging = Logging(delete=True, read=True, write=True, retention_policy=RetentionPolicy(enabled=True, days=7))
        main_deployer.table_service.set_table_service_properties(logging=logging, hour_metrics=hour_minute_metrics, minute_metrics=hour_minute_metrics)

        main_deployer.table_service.create_table(main_deployer.source_table_name)

        main_deployer.deploy_function(
            outputs["catalogAppName"]["value"],
            "{}/data_lake_catalog".format(main_deployer.shared_functions_base_path),
        )

        if (main_deployer.environment == "dev" and location in defaults.PRIMARY_LOCATIONS):
            # If we need to do a history run for the eCRM pipeline, trigger that.
            if run_history:
                window_end = dt.now().strftime("%m/%d/%y, %H:%M:%S")
                logger.info(f"Running history load for eCRM replication pipeline with end time {window_end}.")
                run_response = main_deployer.adf_client.pipelines.create_run(
                    main_deployer.resource_group,
                    adf_name,
                    "eCRMReplicate",
                    parameters={
                        # "windowStartTime": "1/1/70, 00:00:00 PM",
                        # "windowEndTime": window_end
                    }
                )

                # Wait for the pipeline to finish before starting the trigger.
                pipeline_status = "InProgress"
                while pipeline_status == "InProgress":
                    time.sleep(30)
                    run = main_deployer.adf_client.pipeline_runs.get(main_deployer.resource_group, adf_name, run_response.run_id)
                    pipeline_status = run.status

                # Raise an error if it fails.
                if pipeline_status != "Succeeded":
                    raise Exception("History pipeline run for eCRM failed.")

            # Reactivating ADF trigger for eCRM replication.
            main_deployer.adf_client.triggers.start(
                main_deployer.resource_group,
                adf_name,
                "eCRMReplicateTrigger"
            )

        return True
    return False
