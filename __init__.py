##############################################################################
#
# Name: azuredatabricks.py
# Usage: Defines classes for Azure Databricks Clusters and Jobs for UDP.
#        Based on Databricks API v2.0
#
##############################################################################

import requests
from requests.adapters import HTTPAdapter
from requests.packages.urllib3.util.retry import Retry
import getpass
import os
import sys
import json
import pandas as pd
import pyodbc
import re
import logging
import base64
import http.client
import urllib.request
import urllib.parse
import urllib.error

logger = logging.getLogger()
logger.setLevel(logging.INFO)

requests_log = logging.getLogger("requests.packages.urllib3")
requests_log.setLevel(logging.DEBUG)
requests_log.propagate = True


class BasicClient:
    def __init__(self, url):
        self.session = self.requests_retry_session(url)

    def requests_retry_session(
        self,
        url,
        retries=5,
        backoff_factor=1.5,
        status_forcelist=[500, 502, 503, 504, 429],
        method_whitelist=frozenset(["POST", "GET", "PATCH", "PUT", "DELETE"]),
        session=None,
    ):
        session = session or requests.Session()
        retry = Retry(
            total=retries,
            read=retries,
            connect=retries,
            backoff_factor=backoff_factor,
            status_forcelist=status_forcelist,
            method_whitelist=method_whitelist
        )
        adapter = HTTPAdapter(
            max_retries=retry,
            pool_maxsize=100,
            pool_connections=2
        )
        session.mount('http://', adapter)
        session.mount('https://', adapter)
        session.mount(url, adapter)

        return session


#####################################################################
#Create Databricks Workspace
#
######################################################################

class DatabricksWorkspace(BasicClient):
    def __init__(
        self,
        url,
        workspace,
        databricks_token,
        app_ad_group_id,
        group_name
    ):
        self.url = url
        self.workspace = workspace
        self.databricks_token = databricks_token
        self.app_ad_group_id = app_ad_group_id
        self.group_name = group_name
        super().__init__(url)

        self.header = {
            "Accept": "application/scim+json",
            "Content-Type": "application/scim+json",
            "Authorization": f"Bearer {self.databricks_token}"
        }
   # Create Databricks AD Group #
    
    def create_databricks_ad_groups(self):
        group_url = f"{self.url}/api/2.0/preview/scim/v2/Groups"

        payload = {
            "schemas": [
                "urn:ietf:params:scim:schemas:core:2.0:Group"
            ],
            "displayName": self.group_name
        }

        try:
            group_resp = self.session.post(
                group_url, 
                headers=self.header, 
                json=payload
            )
            logger.info("Creating Databricks AD Group")
            return group_resp
        
        except Exception as e:
            raise e
    
    # Extract Databricks Users from AD using appGroupId#

    def extract_databricks_ad_users(self):
        #Extract the Users from AD using Microsoft Graph API
        headers = {
            "Authorization": f"Bearer {self.databricks_token}"
        }
        params = urllib.parse.urlencode({
            'api-version': '1.6',
        })
        try:
            conn = http.client.HTTPSConnection('graph.windows.net')
            conn.request("GET", "/jll2.onmicrosoft.com/groups/fe6beb49-7688-4643-9df0-c02a482ea339/$links/members?%s" % params, "", headers)
            response = conn.getresponse()
            data = response.read()
            return (data.json)
            conn.close()
        except Exception as e:
            raise e
        
        with open('data.json', 'r') as f:
            users_dict = json.loads(f)
        for users in users_dict:
            return users_dict(users['userPrincipalName'])
            
        users_url = f"{self.url}/api/2.0/preview/scim/v2/Users"
        payload = {
            "schema": ["urn:irtf:params:scim:schemas:core:2.0:Users"],
            "userName": f"users_dict()",
             "groups": f"group_resp"
        }

        try:
            user_resp = self.session.post(
                url=users_url, 
                headers=self.header, 
                json=payload
            )
            logger.info("Creating Databricks AD Users")
            return user_resp
        
        except Exception as e:
            raise e

    
    def add_databicks_ad_users(self):
        
        payload = {
            "schema":["urn:ietf:params:scim:api:messages:2.0:Patchop"],
            "Operations": [
                {"op": "add",
                    "value": {
                        "members": [{"value": user_resp}]
                    }}
            ] 
        }
        try:
                gppatch_resp = self.session.patch(
                    url=self.group_url, 
                    headers=self.header, 
                    json=payload
                )
                logger.info("Adding Databricks AD Users to Support Group")
        
        except Exception as e:
            raise e

######################################################################
#
#
######################################################################
class DatabricksCluster(BasicClient):

    spark_conf = '{"spark.databricks.cluster.profile":"serverless", "spark.databricks.repl.allowedLanguages":"sql,python"}'
    spark_ver = "5.3.x-scala2.11"

    def __init__(
        self,
        cluster_name,
        url,
        header,
        cluster_id=None,
        spark_env_vars='{"PYSPARK_PYTHON": "/databricks/python3/bin/python3"}',
        node_type_id="Standard_DS3_v2",
        min_workers=1,
        max_workers=3,
        autotermination_minutes=30,
        custom_tags='{"ResourceClass":"Serverless"}'
    ):
        self.cluster_name = cluster_name
        self.url = url
        self.header = header
        self.cluster_id = cluster_id
        self.spark_env_vars = spark_env_vars
        self.spark_version = DatabricksCluster.spark_ver
        self.node_type_id = node_type_id
        self.min_workers = min_workers
        self.max_workers = max_workers
        self.autotermination_minutes = autotermination_minutes
        self.custom_tags = custom_tags
        self.worker_config = self.set_cluster_scale()
        self.cluster_configs = self.set_configs()
        super().__init__(url)

    def set_cluster_scale(self):
        ###################################################################################
        # Set the cluster workers attributes for fixed workers or auto-scale
        ###################################################################################
        if self.min_workers == self.max_workers:
            worker_config = '"num_workers":' + str(self.min_workers)

        else:

            if self.min_workers > self.max_workers:
                raise Exception('Minimum workers must be less than Maximum workers')
            else:
                worker_config = '"autoscale":{"min_workers": ' + str(self.min_workers) + ', "max_workers":' + str(self.max_workers) + '}'

        return worker_config

    def set_configs(self):
        ###################################################################################
        # Set the cluster configurations
        ###################################################################################
        cluster_configs = '"spark_version":"' + DatabricksCluster.spark_ver + '", "node_type_id":"' + self.node_type_id
        cluster_configs = cluster_configs + '", "custom_tags":' + self.custom_tags
        cluster_configs = cluster_configs + ', "spark_env_vars":' + self.spark_env_vars + ', ' + self.set_cluster_scale() + ', '
        cluster_configs = cluster_configs + '"autotermination_minutes":' + str(self.autotermination_minutes)
        return cluster_configs

    def build_data(self):
        ###################################################################################
        # Build the cluster data for API calls
        ###################################################################################
        cluster_configs = self.set_configs()

        if self.cluster_id is None or self.cluster_id == '':
            cluster_id = ''

        else:
            cluster_id = '"cluster_id": "' + self.cluster_id + '",'

        cluster_data = '{' + cluster_id + '"cluster_name": "' + self.cluster_name + '", '
        cluster_data = cluster_data + cluster_configs + ', "spark_conf":' + DatabricksCluster.spark_conf + '}'
        return json.loads(cluster_data)

    def create(self):
        ###################################################################################
        # Create a physical Databricks cluster
        ###################################################################################
        cluster_data = self.build_data()
        create_url = "{}/api/2.0/clusters/create".format(self.url)

        try:
            resp = self.session.post(create_url, headers=self.header, json=cluster_data)

            self.cluster_id = resp.json()['cluster_id']
            logger.info("Creating cluster {}".format(self.cluster_name))

        except Exception as e:
            logger.info("Request failed. Check URL and token.")
            raise e

    def update(self):
        ###################################################################################
        # Update (edit) a physical Databricks cluster
        ###################################################################################
        cluster_data = self.build_data()
        edit_url = "{}/api/2.0/clusters/edit".format(self.url)

        try:
            resp = self.session.post(edit_url, headers=self.header, json=cluster_data)

            logger.info("Updating cluster {}".format(self.cluster_name))
            return resp.json()

        except:
            logger.info("Request failed. Check URL and token.")

    def terminate(self):
        ###################################################################################
        # Terminates a Spark cluster given its id. The cluster is removed asynchronously.
        # Once the termination has completed, the cluster will be in a TERMINATED state.
        # If the cluster is already in a TERMINATING or TERMINATED state, nothing will happen.
        ###################################################################################

        cluster = json.loads('{"cluster_id": "' + self.cluster_id + '"}')
        delete_url = "{}/api/2.0/clusters/delete".format(self.url)

        try:
            resp = self.session.post(delete_url, json=cluster, headers=self.header)

            logger.info("Terminating cluster {}".format(self.cluster_name))

            return resp.json()

        except:
            logger.info("Request failed. Check URL and token.")

    def permanent_delete(self):
        ###################################################################################
        # Removes a Spark cluster given its id. Permanently delete a cluster.
        # If the cluster is running, it is terminated and its resources are
        # asynchronously removed. If the cluster is terminated, then it
        # is immediately removed.
        ###################################################################################

        cluster = json.loads('{"cluster_id": "' + self.cluster_id + '"}')
        delete_url = "{}/api/2.0/clusters/permanent-delete".format(self.url)

        try:
            resp = self.session.post(delete_url, json=cluster, headers=self.header)

            logger.info("Deleting cluster {}".format(self.cluster_name))

            return resp.json()

        except:
            logger.info("Request failed. Check URL and token.")

    def get_info(self):
        ###################################################################################
        # Retrieve the configuration of a cluster
        ###################################################################################
        get_url = self.url + "/api/2.0/clusters/get?cluster_id=" + self.cluster_id

        try:
            resp = self.session.get(get_url, headers=self.header)

            return resp.json()

        except:
            logger.info("Request failed. Check URL and token.")

    def get_state(self):
        ###################################################################################
        # Retrieve the current state of a cluster
        ###################################################################################
        get_url = self.url + "/api/2.0/clusters/get?cluster_id=" + self.cluster_id

        try:
            resp = self.session.get(get_url, headers=self.header)

            return resp.json()['state']

        except:
            logger.info("Request failed. Check URL and token.")


class JobNotFoundException(Exception):
    """
    Exception raised if a job isn't found.
    """
    pass


class JobAlreadyRunningException(Exception):
    """
    Exception raised if job submission would be skipped.
    """
    pass


####################################################################################################
# Defines the DatabricksJob class variables and methods
#
# A DatabricksJob is uniquely identified by its job_id, which is assigned when the job is created
# in Databricks (either manually or through the API). A valid name, URL, header, and cluster
# configurations are needed in order to use the methods.
#
# A DatabricksJob exists in a DatabricksWorkspace and is attached to a DatabricksCluster.
####################################################################################################
class DatabricksJob(BasicClient):

    def __init__(
            self, job_name, url, header, libraries, parameters=None, schedule=None,
            python_file=None, max_retries=None, min_retry_interval_millis=None, max_concurrent_runs=None
    ):
        self.job_name = job_name
        self.url = url
        self.header = header
        self.cluster_config = None
        self.job_id = None
        self.libraries = libraries
        self.parameters = None
        self.schedule = None
        self.python_file = None
        self.cluster_config = None
        self.max_retries = max_retries
        self.min_retry_interval_millis = min_retry_interval_millis
        self.max_concurrent_runs = max_concurrent_runs
        self.email_notifications = None
        super().__init__(url)

        try:
            self._get_from_name()

        except JobNotFoundException:
            logger.info("Job with name {} not found. It must be created.".format(self.job_name))

    def _get_settings(self):
        ###################################################################################
        # Get job settings and details
        ###################################################################################
        get_url = self.url + "/api/2.0/jobs/get?job_id=" + str(self.job_id)

        resp = self.session.get(get_url, headers=self.header)
        if not resp.ok:
            resp.raise_for_status()
        settings = resp.json()["settings"]
        self.cluster_config = settings.get("new_cluster") or settings.get("existing_cluster")
        self.python_file = settings["spark_python_task"]["python_file"]
        self.parameters = settings["spark_python_task"].get("parameters")
        self.max_retries = settings.get("max_retries")
        self.min_retry_interval_millis = settings.get("min_retry_interval_millis")
        self.max_concurrent_runs = settings.get("max_concurrent_runs")
        self.schedule = settings.get("schedule")

    def _get_from_name(self):
        jobs_url = "{}/api/2.0/jobs/list".format(self.url)
        response = self.session.get(jobs_url, headers=self.header)

        if not response.ok:
            response.raise_for_status()

        jobs = response.json().get("jobs", [])
        for job in jobs:
            if job["settings"]["name"] == self.job_name:
                self.job_id = job["job_id"]
                logger.info("Found job with ID {}. Getting current settings.".format(self.job_id))

                # Getting job settings for job.
                self._get_settings()
                break

        else:
            raise JobNotFoundException("Could not find job with name {}".format(self.job_name))

    def build_data(self):
        ###################################################################################
        # Build the job data for API calls
        ###################################################################################

        # Build job data
        job_data = {
            "name": self.job_name,
            "new_cluster": self.cluster_config
        }

        # Set optional settings if specified
        if self.libraries:
            job_data["libraries"] = self.libraries

        if self.python_file:
            job_data["spark_python_task"] = {}
            job_data["spark_python_task"]["python_file"] = self.python_file
            job_data["spark_python_task"]["parameters"] = self.parameters

        if self.schedule:
            job_data["schedule"] = self.schedule

        if self.max_retries:
            job_data["max_retries"] = self.max_retries

        if self.min_retry_interval_millis:
            job_data["min_retry_interval_millis"] = self.min_retry_interval_millis

        if self.max_concurrent_runs:
            job_data["max_concurrent_runs"] = self.max_concurrent_runs

        if self.email_notifications:
            job_data["email_notifications"] = self.email_notifications

        return job_data

    def create(self):
        ###################################################################################
        # Create a physical Databricks job
        ###################################################################################
        job_data = self.build_data()
        create_url = "{}/api/2.0/jobs/create".format(self.url)

        logger.info("Creating job {}".format(self.job_name))
        resp = self.session.post(create_url, json=job_data, headers=self.header)

        if not resp.ok:
            resp.raise_for_status()

        self.job_id = resp.json()['job_id']

    # Clean-Up Databricks jobs from workspace which have been removed from config for batch folder.
    def cleanup(self, configJobs=[]):
        jobs_url = "{}/api/2.0/jobs/list".format(self.url)
        response = self.session.get(jobs_url, headers=self.header)

        if response.ok:
            jobs = response.json().get("jobs", [])
            for job in jobs:
                if job["settings"]["name"] not in configJobs:
                    # if job["settings"]["name"] == self.job_name:
                    self.job_id = job["job_id"]
                    logger.info("Found job with ID {}. Deleting...".format(
                        self.job_id))
                    self.delete()

    def delete(self):
        ###################################################################################
        # Delete a physical Databricks job
        ###################################################################################
        delete_url = "{}/api/2.0/jobs/delete".format(self.url)
        pass_json = {
            "job_id": str(self.job_id)
        }

        try:
            logger.info("Deleting job with ID {}".format(self.job_id))

            resp = self.session.post(delete_url, json=pass_json, headers=self.header)

            if not resp.ok:
                resp.raise_for_status()

        except Exception:
            logger.info("Request failed. Check URL and token.")

    def update(self):
        ###################################################################################
        # Update/reset a physical Databricks job
        ###################################################################################
        job_data = self.build_data()
        pass_json = {
            "job_id": str(self.job_id),
            "new_settings": job_data
        }
        reset_url = "{}/api/2.0/jobs/reset".format(self.url)

        logger.info("Updating job with ID {}".format(self.job_id))
        resp = self.session.post(reset_url, json=pass_json, headers=self.header)

        if not resp.ok:
            resp.raise_for_status()

    def create_or_update(
            self, cluster_config, python_file=None, parameters=None,
            schedule=None, max_concurrent_runs=1, max_retries=1,min_retry_interval_millis=0, email_notifications=None
    ):
        if not python_file:
            raise Exception("Please specify Python file.")

        self.cluster_config = cluster_config
        self.python_file = python_file
        self.parameters = parameters
        self.schedule = schedule
        self.max_concurrent_runs = max_concurrent_runs
        self.max_retries = max_retries
        self.min_retry_interval_millis = min_retry_interval_millis
        if email_notifications:
            self.email_notifications = email_notifications

        if self.job_id:
            logger.info("Job with ID {} already exists. Updating.".format(self.job_id))
            self.update()

        else:
            logger.info("Job with name {} doesn't exist. Creating.".format(self.job_name))
            self.create()

        self._get_settings()
        return self.job_id

    def run(self, arguments=None):
        ###################################################################################
        # Run a job
        ###################################################################################
        run_url = "{}/api/2.0/jobs/run-now".format(self.url)
        data = {
            "job_id": self.job_id
        }
        if arguments:
            data["python_params"] = arguments

        if self.max_retries == 1 and self.is_running():
            raise JobAlreadyRunningException(
                f"Job with name {self.job_name} is already running and max retry = 1."
            )

        # Job submission would be skipped if active job already exists
        if self.max_concurrent_runs == 1 and self.is_running():
            raise JobAlreadyRunningException(
                f"Job with name {self.job_name} is already running and max conncurency = 1."
            )

        resp = self.session.post(run_url, json=data, headers=self.header)

        logger.info("Running job with ID {}".format(self.job_id))
        return resp.json().get("run_id")

    def is_running(self):
        ###################################################################################
        # Check if job is actively running
        ###################################################################################
        check_url = f"{self.url}/api/2.0/jobs/runs/list?job_id={self.job_id}&active_only=true"
        resp = self.session.get(check_url, headers=self.header)

        try:
            # Active job found
            last_run = resp.json()['runs'][0]
            run_id = last_run['run_id']
            logger.info(f"Running job found with run ID {run_id}")
            return True
        except KeyError:
            # No active job found
            return False
    
    def add_grants(self):
        group_resp.json = self.group_resp
        grants_url = f"{self.url}/permission/jobs/{self.job_id}"

        acl_lists = {
            "group_name": format(self.group_resp),
            "permission_level": "CanManageRunObject"
        }
        try:
            grants_response = requests.post(grants_url, acl_lists)
        except Exception as e:
            raise e




####################################################################################################
# Defines the DatabricksFS class variables and methods
#
# These utilities are used for interacting with DBFS in the current workspace.
#
####################################################################################################
class DatabricksFS(BasicClient):
    def __init__(self, url, header):
        self.url = url
        self.header = header
        super().__init__(url)


    def test(self):
        resp = self.session.post("http://httpstat.us/503")
        if not resp.ok:
            logger.info(resp.status_code)
            resp.raise_for_status()

     # Clean-Up Databricks jobs from workspace which have been removed from config for batch folder.
    def cleanup(self, configJobs=[]):
        jobs_url = "{}/api/2.0/jobs/list".format(self.url)
        response = self.session.get(jobs_url, headers = self.header)
       
        if response.ok:
            jobs = response.json().get("jobs", [])
            for job in jobs:
                if job["settings"]["name"] not in configJobs:
                    # if job["settings"]["name"] == self.job_name:
                    self.job_id = job["job_id"]
                    logger.info("Found job with ID {}. Deleting...".format(self.job_id))
                    self.delete()

    # Delete a physical Databricks job
    def delete(self):
        delete_url = "{}/api/2.0/jobs/delete".format(self.url)
        pass_json = {
            "job_id": str(self.job_id)
        }
        
        try:
            logger.info("Deleting job with ID {}".format(self.job_id))

            resp = self.session.post(delete_url, json = pass_json, headers = self.header)
            
            if not resp.ok:
                resp.raise_for_status()

        except:
            logger.info("Request failed. Check URL and token.")

    def mkdirs(self, path):
        mkdirs_url = "{}/api/2.0/dbfs/mkdirs".format(self.url)
        data = {
            "path": path.replace("dbfs://", "/")
        }

        logger.info("Making path {}.".format(path))
        resp = self.session.post(mkdirs_url, headers=self.header, json=data)
        if not resp.ok:
            logger.info(resp.status_code)
            resp.raise_for_status()

    def _put(self, path, file, overwrite=False, file_name=None):
        put_url = "{}/api/2.0/dbfs/put".format(self.url)
        with open(file, mode="rb") as f:
            content = f.read()
        if overwrite:
            overwrite_str = "true"
        else:
            overwrite_str = "false"

        if not file_name:
            file_name = os.path.basename(file)

        encoded_content = base64.b64encode(content).decode('utf-8')
        data = {
            "path": "{}/{}".format(path.replace("dbfs://", "/"), file_name),
            "overwrite": overwrite_str,
            "contents": encoded_content
        }

        logger.info("Uploading file {}.".format(os.path.basename(file)))
        response = self.session.post(put_url, headers=self.header, json=data)

        if not response.ok:
            response.raise_for_status()

    def _put_streaming(self, path, file, overwrite=False, file_name=None):
        """
        Use the Databricks streaming API to upload a file that may be larger
        than 1 MB.  See
        https://docs.databricks.com/dev-tools/api/latest/examples.html#upload-a-big-file-into-dbfs
        for more information.
        """
        base_url = "{}/api/2.0/dbfs/".format(self.url)
        if not file_name:
            file_name = os.path.basename(file)

        # Create streaming handle
        response = self.session.post(
            base_url + 'create',
            headers=self.header,
            json={
                "path": "{}/{}".format(path.replace("dbfs://", "/"), file_name),
                "overwrite": str(overwrite).lower(),
            }
        )
        if not response.ok:
            response.raise_for_status()
        handle = response.json()['handle']

        # Add file in blocks
        logger.info("Uploading file {}.".format(os.path.basename(file)))
        with open(file, mode="rb") as f:
            while True:
                # A block can be at most 1 MB
                content = f.read(1 * 1024 * 1024)
                if not content:
                    break
                encoded_content = base64.b64encode(content).decode('utf-8')
                response = self.session.post(
                    base_url + 'add-block',
                    headers=self.header,
                    json={"handle": handle, "data": encoded_content}
                )
                if not response.ok:
                    response.raise_for_status()

        # Close the handle
        response = self.session.post(
            base_url + 'close',
            headers=self.header,
            json={"handle": handle}
        )
        if not response.ok:
            response.raise_for_status()

    def put(self, path, file, streaming=False, overwrite=False, file_name=None):
        if streaming:
            self._put_streaming(path, file, overwrite, file_name)
        else:
            self._put(path, file, overwrite, file_name)


class DatabricksSecretClient(BasicClient):
    """
    Client for interacting with the Databricks secrets interface.

    Args:
        url: The base URL of the Databricks API.
        header: The authentication header for the API.

    """

    def __init__(self, url, header):
        self.url = url
        self.header = header
        super().__init__(url)

    def create_scope(self, scope_name: str):
        """
        Creates a new scope with the given name.
        If a scope already exists with the given name,
        the method finishes successfully.

        Args:
            scope_name: The name of the scope to create.

        """
        scope_url = "{}/api/2.0/secrets/scopes/create".format(self.url)

        response = self.session.post(scope_url, headers=self.header, json={"scope": scope_name, "initial_manage_principal": "users"})
        if not response.ok:
            if response.json().get("error_code") == "RESOURCE_ALREADY_EXISTS":
                logger.info("Scope already exists.")
            else:
                response.raise_for_status()

    def set_secret(self, scope_name: str, secret_name: str, secret_value: str):
        """
        Create or update a secret with the given value.
        Creates the secret if it doesn't exist, else updates it.

        Args:
            scope_name: The name of the scope to add the secret to.
            secret_name: The name of the secret.
            secret_value: The value to set.

        """
        secret_url = "{}/api/2.0/secrets/put".format(self.url)
        payload = {
            "scope": scope_name,
            "key": secret_name,
            "string_value": secret_value
        }

        if payload['string_value'] is None:
            payload['string_value'] = ''

        response = self.session.post(secret_url, headers=self.header, json=payload)
        if not response.ok:
            logger.error(response.text)
            response.raise_for_status()
