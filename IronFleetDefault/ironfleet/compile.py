import os
import json


dafny_path, nthreads = "", 0
with open("./config.json", "r") as f:
	data = json.load(f)
	dafny_path = data["dafny_path"]
	nthreads = data["nthreads_to_compile"]

cmd = "cd ironfleet && time scons -j {} --dafny-path={}".format(nthreads, dafny_path)
print("[+] running {}".format(cmd))
os.system(cmd)


