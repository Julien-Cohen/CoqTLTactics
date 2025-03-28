from os import listdir, chdir
from os.path import isfile, join, isdir
import subprocess


def read(output):
    with open(output, 'r') as f: 
        last_line = f.readlines()[-1]
        nums = last_line.split(" ")
        nums = [x for x in nums if x]
        spec = int(nums[0])
        impl = int(nums[1])
        comment = int(nums[2])
        return spec+impl

def exec(folderName):
    arg = f"./{folderName}/*.v"
    output = f"./statistics/loc/{folderName}.txt"
    myoutput = open(output, 'w')
    subprocess.run(["coqwc", arg], stdout=myoutput) 
    return read(output)

base_properties_folder = "./core/properties/"
exclude_folders = ['statistics', 'axiomatic', 'unclassified']
chdir(base_properties_folder)

for f in listdir("./"):
    if isdir(f) and f not in exclude_folders:
        loc = exec(f)
        print(f"{f}\t\t\t\t{loc}")





