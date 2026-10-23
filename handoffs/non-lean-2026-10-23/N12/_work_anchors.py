import io,os
n12=os.environ["N12"]
pats={
 "_head/scripts__shell_lint_allowlist.txt":["Shell audit 2026-10-23","all 439","Pin train 2026-10-22","MR8.8 (2026-10-23)","cusps_map","Second bump 2026-10-23","MR9 Thm19/NFKummer","MR9 Thm19/CuspPrincipal","Iut.Frobenioid.TorsorHom.integral"],
 "_head/Iut__Multiradial__ROADMAP.md":["CuspData.inertia","removed (MR8.8","hball_auto","consumed from curves-jacobian","curves-jacobian da434f1","MR8.8 done"],
 "_head/Plans__MR9Plan.md":["hDGC","hL : JacDivFree","Schreier/RH debt","coordinated pin train done","positive multiple","belyi 5f3a88e","da434f1"],
 "_head/Plans__MR10Plan.md":["Debt (rule 4)","Cor23i","Missing:","State: iut main"],
 "_head/lakefile.toml":["continuous-kummer-theory","formal-schemes","elliptic-curves","curves-jacobian","12719c9","7206d78"],
 "_head/lake-manifest.json":["lana-agents/curves-jacobian","continuous-kummer-theory","elliptic-curves","formal-schemes"],
 "_head/Iut__AutHolomorphic__README.md":["MR10Plan.md"],
}
for rel,ps in pats.items():
    p=os.path.join(n12,rel.replace("/",os.sep))
    lines=io.open(p,encoding="utf-8",errors="replace").read().splitlines()
    print("==",rel,"(%d lines)"%len(lines))
    for pat in ps:
        hits=[(i+1,l.strip()[:130]) for i,l in enumerate(lines) if pat in l]
        for i,l in hits[:2]:
            print("  %-30s L%-5d %s"%(pat,i,l))
        if not hits: print("  %-30s <none>"%pat)