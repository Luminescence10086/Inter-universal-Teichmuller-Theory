import io,os,sys,difflib
n12=os.environ["N12"]
def rd(p):
    with io.open(p,encoding="utf-8",errors="replace") as f:
        return f.read().splitlines()
name=sys.argv[1]
b=rd(os.path.join(n12,"_base",name)); h=rd(os.path.join(n12,"_head",name))
d=list(difflib.unified_diff(b,h,fromfile="base/"+name,tofile="head/"+name,lineterm="",n=int(sys.argv[2]) if len(sys.argv)>2 else 3))
out="\n".join(d)
f=os.path.join(n12,"_diffs",name.replace("/","__")+".diff")
os.makedirs(os.path.dirname(f),exist_ok=True)
with io.open(f,"w",encoding="utf-8",newline="\n") as fh:
    fh.write(out+"\n")
print("lines_base=%d lines_head=%d diff_lines=%d -> %s"%(len(b),len(h),len(d),f))
print("added=%d removed=%d"%(sum(1 for x in d if x.startswith("+") and not x.startswith("+++")),sum(1 for x in d if x.startswith("-") and not x.startswith("---"))))