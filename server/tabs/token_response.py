import json

import streamlit as st
from streamlit import session_state as sts

from logging_utils import log_write
from serv_utils import (TASKS, TOKEN_JSON_FILE, get_async_response,
                        show_response, store_token_responses)

st.header("Async Server Response Retrieval")
st.write("Use the token you received earlier to fetch the response from the server.")

st.divider()
st.subheader("Token Information")


def check_token_status():
    try:
        with open(TOKEN_JSON_FILE, "r") as f:
            token_data = json.load(f)
            for token, status in token_data.items():
                if status == "running":
                    err_code, _ = get_async_response(token)
                    if err_code == 0:
                        store_token_responses(token, "completed")
                    elif err_code == 1:
                        pass # still running
                    elif err_code == 2:
                        store_token_responses(token, "error")
                    elif err_code == 3:
                        store_token_responses(token, "parsing_error")
                else:
                    pass # do nothing for error and completed tokens

    except FileNotFoundError:
        token_data = {}
        st.warning("Token JSON file not found.")
    return token_data


token_data = check_token_status()
token_table = {
    "Token" : [token for token in token_data.keys()],
    "Status" : [token_data[token] for token in token_data.keys()]
}

st.table(token_table)

st.divider()

st.subheader("Get Response from Token")

sts.token_server = st.text_input("Enter Token to get response from server:", help="Enter the token you received earlier to fetch the corresponding response from the server.")
if st.button("Get Response from Token", help="Fetch the response from the server using the provided token."):
    if int(sts.token_server.strip()):
        try:
            err_code, lookup_response = get_async_response(sts.token_server.strip())
            if err_code == 1:
                store_token_responses(sts.token_server.strip(), "running")
                st.warning("Response is still being processed. Please try again later.")
            elif err_code == 2:
                store_token_responses(sts.token_server.strip(), "error")
                st.error("Error occurred while fetching the response.")
                st.error(f"Error: {lookup_response.get('error', 'Unknown error')}")

            elif err_code == 3:
                store_token_responses(sts.token_server.strip(), "parsing_error")
                st.warning("Error while parsing response. See it below.")
                st.json(lookup_response)

            else: # err_code == 0, i.e. output recieved from file loaded
                store_token_responses(sts.token_server.strip(), "completed")
                if lookup_response.get("result") == "error":
                    st.error(f"The server returned an error for the provided token. Error: {lookup_response.get('error', 'Unknown error')}")

                    log_write("Streamlit", "Get Response from Token: Server returned error.")
                else: # success
                    try:
                        if "task" in lookup_response.keys():
                            lookup_response["tasks"] = [lookup_response["task"]]
                        sts.selected_tasks = lookup_response.get("tasks", [])
                        sts.selected_tasks = [task for task in TASKS.keys() if TASKS[task]["task_name"] in sts.selected_tasks]
                        sts.result = lookup_response
                        sts.val_input = {k: v for k, v in lookup_response.items() if k not in ["result", "error", "task", "tasks"]}
                        show_response(show_input=True)
                    except Exception as e:
                        st.success("Response fetched successfully from the server. See the output below.")
                        st.warning(f"Error occurred: {e}. See the response below.")
                        st.json(lookup_response)


                    log_write("Streamlit", "Get Response from Token: Success")


        except Exception as e:
            st.error(f"Exception occurred while processing response: {e}")
            log_write("Streamlit", f"Get Response from Token: Exception - {e}")
    else:
        st.warning("Please enter a valid token.")

    st.subheader("View the full JSON Response for the provided token:")
    st.json(lookup_response, expanded=False)

