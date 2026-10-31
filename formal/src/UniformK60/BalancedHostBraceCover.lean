import UniformK60.BalancedHostBraceStart
import UniformK60.BalancedHostBraceRealization
import UniformK60.BalancedEncodingBraceNormalization

/-! Complete actual mixed-profile C2-root coverage of the720 exact brace
inputs. No finite-coverage, fake-template, or host-extension premise remains. -/
set_option autoImplicit false
namespace UniformK60.BalancedHostBraceCover
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization
open UniformK60.BalancedHostBraceStart UniformK60.BalancedHostBraceFrame
open UniformK60.BalancedHostBraceMarked UniformK60.BalancedHostBraceRealization
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedHost
open UniformK60.BalancedEncodingBraces

theorem actual_C2_case (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (r : Vertex) (hw : W c r=31) :
    ∃ d : Host,∃ k : Case,NoMonochromaticTriangle d ∧
      BalancedHost.Normalized false d (owner k) ∧ Core.UnitsMatch d (units k) := by
  obtain ⟨a,good,caps,hd,mark,hm,hh,hfive⟩ := oriented_root c hc hn r hw
  obtain ⟨g,⟨frame⟩⟩ := actual_frame a good r mark hm hh (hd 2) hfive
  obtain ⟨p,i,_,hmat⟩ := actual_projected_cover g frame.frame good
  obtain ⟨m,n,np,nmark⟩ := actual_marked a good r mark (hd 3) hm
  obtain ⟨d,hgood,hdcaps,hu⟩ := realize good caps hd frame p i hmat m n np nmark
  refine ⟨normalized d (target g i) m,(target g i,m),?_,?_,?_⟩
  · exact UnitTransport.transformed_good d hgood _ _
  · exact normalized_from_raw_units d (target g i) m hdcaps hu
  · exact mapped_units_match d (target g i) m hu

#print axioms actual_C2_case
end UniformK60.BalancedHostBraceCover
