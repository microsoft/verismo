import os;
def find(input_string, char):  
    count = 0  
    for c in input_string:  
        if c == char:  
            count += 1  
    return count
def create_file_and_dir(file_name):  
    # Create the directory if it doesn't exist 
    path = os.path.dirname(file_name); 
    if not os.path.exists(path):  
        os.makedirs(path)  
      
    # Create the file in the directory  
    file_path = os.path.join(path, file_name)  
    with open(file_path, 'w') as file:  
        file.write("")  
def find_from_set(input, keywords):
        for k in keywords:
                if k in input:
                        i = input.find(k)
                        if input[i-1].isalpha() or input[i+len(k)].isalpha() or input[i-1]=="_" or input[i+len(k)]=="_":
                                continue
                        print(input, k)
                        return k
        return None
def get_spaces(line):
        out = ""
        for c in line:
                if c.isspace():
                        out += c
                else:
                        break
        return out
key2 = ["proof", "open spec fn", "closed spec fn"]
key1 = ["invariant", "ensures", "requires", "proof", "spec fn"]
def erase(infile: str, outfile:str):
        ghost_count = 0
        exe_count = 0
        ghost_lines = []
        alllines = []
        exe_lines = []
        lines = []
        ghost = False
        exe_fn = 0
        stack = ["",""]
        brackets = 0
        count = 0
        with open(infile, "r") as f:
                for line in f:
                        if line.startswith("use") or line.startswith("//") or line.startswith("pub use"):
                                continue
                        if "ghost" in line:
                                ghost_lines.append(line)
                                continue                            
                        count += 1
                        left = find(line, "{")
                        right = find(line, "}")
                        if stack[-1] in ["invariant", "ensures", "requires"]:
                                stack.append(get_spaces(line))
                                #print("stack", count, stack, get_spaces(line))
                        if stack[-1] in key2 or stack[-1] == "{":
                                while left > right:
                                        stack.append("{")
                                        left = left -1
                                while right > left:
                                        stack.pop()
                                        right = right -1
                        keyword = find_from_set(line, ["invariant", "ensures", "requires", "proof", "open spec fn"])
                        if ghost:
                                if stack[-1] in key2:
                                        ghost = False
                                        stack.pop()
                                        ghost_count = ghost_count + 1
                                        ghost_lines.append(line)
                                        #print("proof ends", line)
                                        continue

                                if  stack[-2] in ["invariant", "ensures", "requires"]:
                                        if not line.startswith(stack[-1]):
                                                ghost = False
                                                stack.pop()
                                                stack.pop()
                                                #print("after pop", stack)
                        if keyword in key2:
                                ghost_count = ghost_count + 1
                                ghost = True
                                stack.append(keyword)
                                while left > right:
                                        stack.append("{")
                                        left = left -1
                                while right > left:
                                        stack.pop()
                                        right = right -1
                                #print("proof starts at", count)
                        elif keyword:
                                ghost = True
                                stack.append(keyword)
                        else:
                                exe_count =  exe_count + 1
                        if ghost:
                                #print("ghost:",line)
                                ghost_lines.append(line)
                        else:
                                #print("exe:",line)
                                exe_lines.append(line)
        ghost_count = len(ghost_lines)
        exe_count = count - ghost_count

        #print("ghost line:", len(ghost_lines), "exe:", count -  len(ghost_lines))
        create_file_and_dir(outfile)
        with open(outfile, "w+") as f:
                f.write("".join(exe_lines))
        return (count, ghost_count, exe_count)


DIRNAME = "/root/snp/verismo/source/monitor_mod/src"

def get_all_files_recursively(directory):  
    all_files = []  
  
    for root, dirs, files in os.walk(directory):  
        for file in files:  
            file_path = os.path.join(root, file)  
            all_files.append(file_path[len(directory)+1:])  
  
    return all_files

def get_files():
        files = []
        filelist = get_all_files_recursively(DIRNAME)
        #for filename in os.listdir(DIRNAME):
        for filename in filelist: 
                if filename.endswith(".rs"):  
                        files.append(filename)
        return files
files = get_files()
arch_count = 0
exe_count = 0
  
for filename in files:
        if ("resource" not in filename) and ("arch" not in filename) and (not filename.startswith("output")) and (not filename.endswith("s.rs")) and (not "spec" in filename) and (not "pervasive" in filename) and (not filename.endswith("p.rs")) and "unverified" not in filename:
                print(filename)
                infile = os.path.join(DIRNAME, filename)
                exe_file = os.path.join(os.path.join(DIRNAME, "output"), filename)
                count, ghost, exe = erase(infile, exe_file)
                arch_count += count
                if "arch" in filename or "resource" in filename:
                        exe = 0
                exe_count += exe

for filename in files:
        allline = []
        allfile_noheader = os.path.join(os.path.join(DIRNAME, "output-all"), filename)
        infile = os.path.join(DIRNAME, filename)
        with open(infile, "r") as f:
                for line in f:
                        if line.startswith("use") or line.startswith("//") or line.startswith("pub use"):
                                continue
                        allline.append(line)
        create_file_and_dir(allfile_noheader)
        with open(allfile_noheader, "w+") as f:
                f.write("".join(allline))
#erase("/root/snp/verismo/source/monitor_mod/src/verismo/alloc/exe.rs", "/root/snp/verismo/source/monitor_mod/src/output/verismo/alloc/exe.rs")
print(arch_count, exe_count)

import subprocess
DIRNAME1 = DIRNAME+"/output"
DIRNAME2 = DIRNAME

print("Rust: alloc")
subprocess.run(["cloc", DIRNAME1+"/verismo/alloc"]) 
subprocess.run(["cloc", DIRNAME2+"/verismo/alloc"]) 

print("Rust:Smart pointer")
subprocess.run(["cloc", DIRNAME1+"/verismo/data", DIRNAME1+"/verismo/global"]) 
subprocess.run(["cloc", DIRNAME2+"/verismo/data", DIRNAME2+"/verismo/global"]) 


print("Rust:Lock")
subprocess.run(["cloc", DIRNAME1+"/verismo/lock"]) 
subprocess.run(["cloc", DIRNAME2+"/verismo/lock"]) 

print("Rust: tspec")
subprocess.run(["cloc", DIRNAME1+"/tspec"]) 
subprocess.run(["cloc", DIRNAME2+"/tspec"]) 

print("Rust:mem")
subprocess.run(["cloc", DIRNAME1+"/verismo/mem", DIRNAME1+"/verismo/snp/rmp", DIRNAME1+"/verismo/state"])
cmd =["cloc", DIRNAME2+"/verismo/mem", DIRNAME2+"/verismo/snp/rmp", DIRNAME2+"/verismo/state"]
subprocess.run(cmd) 
print(cmd)
print("Rust: init")
subprocess.run(["cloc", DIRNAME1+"/verismo/idt", DIRNAME1+"/verismo/init", DIRNAME1+"/verismo/boot",DIRNAME1+"/verismo/mshyper",DIRNAME1+"/verismo/msr", DIRNAME1+"/verismo/snp/cpuid", DIRNAME1+"/verismo/snp/cpu"]) 
subprocess.run(["cloc",DIRNAME1+"/verismo/idt", DIRNAME2+"/verismo/init", DIRNAME2+"/verismo/boot",DIRNAME2+"/verismo/mshyper",DIRNAME2+"/verismo/msr", DIRNAME2+"/verismo/snp/cpuid", DIRNAME2+"/verismo/snp/cpu"])

print("Rust: vmpl")
subprocess.run(["cloc", DIRNAME1+"/verismo/vmpl", DIRNAME1+"/verismo/snp/secret", DIRNAME1+"/crypto", DIRNAME1+"/verismo/snp/ghcb"]) 
subprocess.run(["cloc", DIRNAME2+"/verismo/vmpl", DIRNAME2+"/verismo/snp/secret", DIRNAME1+"/crypto", DIRNAME2+"/verismo/snp/ghcb"])
