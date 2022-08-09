import sys
import json
import os

def add_review_key(json_file_path):
    """
    Add a key called "review" to each json object in the file.
    """
    with open(json_file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
        for item in data:
            item['review'] = ''
    with open(json_file_path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

if __name__=='__main__':
    # Get the path to the json file from the command line arguments.
    json_file_path = sys.argv[1]
    print("Adding `review` key to {}".format(json_file_path))
    add_review_key(json_file_path)
    print("Done.")
