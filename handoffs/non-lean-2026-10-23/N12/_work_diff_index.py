import io,os
base=os.path.join(os.environ["N12"],"_ls_tree_base.txt")
head=os.path.join(os.environ["N12"],"_ls_tree_head.txt")
def load(p):
    d={}
    with io.open(p,encoding="utf-8") as f:
        for line in f:
            line=line.rstrip("\n")
            if not line: continue
            meta,path=line.split("\t",1)
            mode,typ,sha=meta.split()
            d[path]=sha
    return d
b=load(base); h=load(head)
added=sorted(set(h)-set(b)); deleted=sorted(set(b)-set(h))
mod=sorted(p for p in set(b)&set(h) if b[p]!=h[p])
out=[]
out.append("ADDED %d"%len(added))
for p in added: out.append("  A %s %s"%(h[p],p))
out.append("DELETED %d"%len(deleted))
for p in deleted: out.append("  D %s %s"%(b[p],p))
out.append("MODIFIED %d"%len(mod))
for p in mod: out.append("  M %s -> %s %s"%(b[p],h[p],p))
txt="\n".join(out)+"\n"
with io.open(os.path.join(os.environ["N12"],"diff_index.txt"),"w",encoding="utf-8",newline="\n") as f:
    f.write(txt)
print(txt)
print("TOTAL changes:",len(added)+len(deleted)+len(mod))