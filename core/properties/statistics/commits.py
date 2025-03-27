from os import makedirs
from os.path import isfile, join, isdir, exists
import subprocess

def exec(folderName, alias):
    arg = f"{alias}"

    directory = f"{base}/{folderName}"
    if not exists(directory):
        makedirs(directory)

    output = f"{directory}/{alias}.txt"
    myoutput = open(output, 'w')
    subprocess.run(["git", "log", "-S", arg, "--oneline"], stdout=myoutput) 


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
    for alias in prop:
        exec(prop_name, alias)





