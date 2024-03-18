
# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License.

# You may need the below as well
# pip install pipenv
# pipenv install requests
# <importsAndVars>
import json
import os
from pprint import pprint
import requests 
import sys

'''
This sample uses the Bing Custom Search API to search for a query topic and get back user-controlled web page results.
Bing Custom Search API: https://docs.microsoft.com/en-us/bing/search-apis/bing-custom-search/overview 
'''

# Add your Bing Custom Search subscription key and endpoint to your environment variables.
subscriptionKey = os.environ['BING_CUSTOM_SEARCH_SUBSCRIPTION_KEY']
endpoint = os.environ['BING_CUSTOM_SEARCH_ENDPOINT']
customConfigId = os.environ["BING_CUSTOM_CONFIG"]  # you can also use "1"
searchTerm = sys.argv[1]  # the search term for the query
# </importsAndVars>
# <url>
# Add your Bing Custom Search endpoint to your environment variables.
# url = endpoint + "/bingcustomsearch/v7.0/search?q=" + searchTerm + "&customconfig=" + customConfigId
url = 'https://api.bing.microsoft.com/v7.0/custom/search?' + 'q=' + searchTerm + '&' + 'customconfig=' + customConfigId
# </url>
# <request>
r = requests.get(url, headers={'Ocp-Apim-Subscription-Key': subscriptionKey})
pprint(json.loads(r.text))
# </request>
