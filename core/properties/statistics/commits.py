from os import makedirs
from os.path import isfile, join, isdir, exists
import subprocess

def read(output):
    with open(output, 'r') as f: 
        lines = f.readlines()
        tags = []
        for line in lines:
            line_ = line.split(" ")
            tag = str(line_[0])
            descript = str(line_[1])
            tags.append(tag)
        return tags

def exec(folderName, alias):
    arg = f"{alias}"

    directory = f"{base}/{folderName}"
    if not exists(directory):
        makedirs(directory)

    output = f"{directory}/{alias}.txt"
    myoutput = open(output, 'w')
    subprocess.run(["git", "log", "-S", arg, "--oneline"], stdout=myoutput) 
    return read(output)


base = f"./core/properties/statistics/commits"

dependencies=[
    ['additivity'],
    ['backward_traceability', 'surjectivity'],
    ['confluence'],
    ['distributivity'],
    ['forward_traceability', 'totality'],
    ['injectivity'],
    ['monotonicity'],
    ['surjectivity'],
    ['universality']
]

for prop in dependencies:
    prop_name = prop[0]
    sum_ = set()
    for alias in prop:
        commits = exec(prop_name, alias)
        sum_ = sum_.union(set(commits))
    print(f"{prop_name}\t\t\t\t{len(list(sum_))}")





