import IUTAudit.Scale
namespace IUTAudit.Descent
def hiddenHelper : PLift True := ⟨IUTAudit.Scale.hidden_base⟩
theorem visible : True := hiddenHelper.down
end IUTAudit.Descent
