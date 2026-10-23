import io,os,collections
n12=os.environ["N12"]
def stats(p):
    c=collections.Counter(); n=0
    with io.open(p,encoding="utf-8",errors="replace") as f:
        for line in f:
            line=line.rstrip("\n")
            if not line.strip() or line.startswith("#"): continue
            n+=1
            tag=line.rsplit("\t",1)[-1] if "\t" in line else "<notab>"
            c[tag]+=1
    return n,c
for side in ("_base","_head"):
    p=os.path.join(n12,side,"scripts__shell_lint_allowlist.txt")
    n,c=stats(p)
    print(side,"entries=",n,dict(c))