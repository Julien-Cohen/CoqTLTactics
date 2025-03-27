from os import listdir, chdir
from os.path import isfile, join, isdir
import subprocess

def exec(folderName):
    arg = f"./{folderName}/*.v"
    output = f"./statistics/loc/{folderName}.txt"
    myoutput = open(output, 'w')
    subprocess.run(["coqwc", arg], stdout=myoutput) 

base_properties_folder = "./core/properties/"
exclude_folders = ['statistics', 'axiomatic', 'unclassified']
chdir(base_properties_folder)

for f in listdir("./"):
    if isdir(f) and f not in exclude_folders:
        exec(f)





