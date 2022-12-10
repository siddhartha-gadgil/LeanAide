import requests

URL = "https://en.wikipedia.org/w/api.php"

def get_category_members(category, titles, categories):
    PARAMS = {
        "action": "query",
        "format": "json",
        "list": "categorymembers",
        "cmtitle": category,
        "cmlimit": "max", # Set the limit to "max" to retrieve all the members of the category
        "delay": 0.25
    }

    response = requests.get(url=URL, params=PARAMS)
    data = response.json()

    members = data["query"]["categorymembers"]
    print(category, len(members))

    for item in members:
        if item["ns"] == 14: # Check if the item is a category
            if item["title"] not in categories: # Check if the category has already been processed
                categories.append(item["title"])
                get_category_members(item["title"], titles, categories) # Recursively call the function
        else:
            # Check if the title is already in the list (to avoid duplicates)
            if item["title"] not in titles:
                titles.append(item["title"])

titles = []
categories = []
get_category_members("Category:Mathematical_concepts", titles, categories)

# Write the titles and categories to separate files
with open("../data/wikipedia_math_titles.txt", "w") as f:
    for title in titles:
        f.write(title + "\n")

with open("wikipedia_math_categories.txt", "w") as f:
    for category in categories:
        f.write(category + "\n")
