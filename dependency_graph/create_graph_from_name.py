import json
from queue import Queue
import argparse
from args import build_parser
import subprocess

parser = build_parser()
args = parser.parse_args()

q =  Queue()
result = json.load(open("deps_copy_rep.json","r"))
edge_list_defn = []
edge_list_type = []
name = args.decl_name
defns = list(set(result[name]["defn"]))
types = list(set(result[name]["type"]))
ele_defn = (name,defns)
ele_type = (name,types)
edge_list_defn.append(ele_defn)
edge_list_type.append(ele_type)
for entry in defns:
    q.put(entry)
for entry in types:
    q.put(entry)
while not q.empty():
    name = q.get()
    try:
        defns = list(set(result[name]["defn"]))
        types = list(set(result[name]["type"]))
        ele_defn = (name,defns)
        ele_type = (name,types)
        edge_list_defn.append(ele_defn)
        edge_list_type.append(ele_type)
        for elem in defns:
            q.put(elem)
        for elem in types:
            q.put(types)
    except:
        continue

graph = "strict digraph { \n"
for entry in edge_list_defn:
    if len(entry[1]) == 0:
        continue
    for i,ele in enumerate(entry[1]):
        entry[1][i] = "\""+str(ele)+"\" [color=green]"
    res = "{" + ' '.join(entry[1]) + "}"
    graph = graph + "\t\"{}\" -> {}\n".format(entry[0],res)

for entry in edge_list_type:
    if len(entry[1]) == 0:
        continue
    for i,ele in enumerate(entry[1]):
        entry[1][i] = "\""+str(ele)+"\" [color=blue]"
    res = "{" + ' '.join(entry[1]) + "}"
    graph = graph + "\t\"{}\" -> {}\n".format(entry[0],res)

graph = graph + "\t}"


dot_file = open("{}.dot".format(args.output),"w")
dot_file.write(graph)
dot_file.close()

with open(args.output+".svg","w") as f:
    ret = subprocess.run(["dot","-Tsvg",args.output+".dot"],stdout=f)