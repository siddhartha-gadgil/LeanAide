# Fetch the first page of results from a Google search on `mathlib`.

import sys
import webbrowser
import requests
from bs4 import BeautifulSoup

# Does not work due to restrictions of Google on web-scraping
def google_search(search_term):
    url = 'https://www.google.com/search?sitesearch=https://leanprover-community.github.io/mathlib_docs&q=' + search_term
    # https://docs.python-requests.org/en/master/user/quickstart/#custom-headers
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/100.0.4896.79 Safari/537.36Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:35.0) Gecko/20100101 Firefox/35.0",}

    response = requests.get(url, headers=headers, timeout=30)
    soup = BeautifulSoup(response.text, 'html.parser')
    html = response.text
    soup = BeautifulSoup(html, 'html.parser')
    links = soup.find_all('a')

    filepaths = []

    for link in links:
        if 'href' in link.attrs:
            # Try to find the first link that is a mathlib page
            try:
                (_, tail) = link.attrs['href'].split('leanprover-community.github.io/mathlib_docs/')
                (path, _) = tail.split('.html')
                filepaths.append(path)
            except: continue

    return filepaths

def tests():
    queries = [
        "Every subgroup of a free group is free",
        "A field of characteristic 0 is infinite",
        "The square root of an irrational number is irrational",
        "Every continuous function is differentiable",
        "A finite topological space is compact",
        "A torsion-free group is Abelian",
        "A ring with all elements idempotent is commutative"
    ]

    # Write the output of `google_search` on each of the queries to a file called `google_search_results.md`
    with open('../data/google_search_results.md', 'w') as f:
        for query in queries:
            f.write('# ' + query + '\n')
            for path in google_search(query):
                f.write('- ' + path + '\n')
            f.write('\n')

def main():
    if len(sys.argv) > 1:
        search_term = ' '.join(sys.argv[1:])
    else:
        search_term = input('Search term: ')

    for path in google_search(search_term):
        print(path)