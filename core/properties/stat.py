import subprocess

base = './'
folders = ['additivity', 'confluence', 'distributivity', 'injectivity', 'monotonicity', 'surjectivity', 'totality', 'universality']
type = "/*.v"

for folder in folders:
    folder = base + folder + type
    cmd = ['coqwc', '-p', folder]
    subprocess.call(cmd)