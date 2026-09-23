import PricingC.U15SupportData
namespace PricingC.U15SupportCover
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem support_as_sublist (s:Finset V) (k:Nat) (hk:s.card=k):
 ∃xs∈(List.finRange 15).sublistsLen k,xs.toFinset=s:=by
 let xs:=(List.finRange 15).filter fun v=>v∈s
 have hsub:List.Sublist xs (List.finRange 15):=List.filter_sublist
 have hnd:xs.Nodup:=(List.nodup_finRange 15).sublist hsub
 have hset:xs.toFinset=s:=by ext v;simp [xs]
 have hlen:xs.length=k:=by rw [←List.toFinset_card_of_nodup hnd,hset,hk]
 exact ⟨xs,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,hset⟩

/-- Exact list identity exhausts every4-subset, rather than enumerating only
a prefiltered list assumed to contain every admissible physical support. -/
theorem four_entries_complete : entries4.reverse.map Prod.fst=(List.finRange 15).sublistsLen 4:=by decide +kernel

theorem all_four_checked : entries4.all (fun entry=>
 decide (ProperFour entry.1.toFinset → entry.1.toFinset.image (autoMap entry.2)∈representatives4))=true:=by decide +kernel

theorem four_support_cover (s:Finset V) (hc:s.card=4) (hp:ProperFour s):
 ∃r∈representatives4,∃e:V≃V,(∀a b,a≠b → T (e a) (e b)=T a b) ∧ s.image e=r:=by
 obtain ⟨xs,hxs,hset⟩:=support_as_sublist s 4 hc
 rw [←four_entries_complete] at hxs
 obtain ⟨⟨ys,i⟩,hy,hys⟩:=List.mem_map.mp hxs
 have hy':(ys,i)∈entries4:=List.mem_reverse.mp hy
 have hh:=of_decide_eq_true ((List.all_eq_true.mp all_four_checked) (ys,i) hy')
 change ys=xs at hys
 subst ys
 rw [hset] at hh
 exact ⟨s.image (autoMap i),hh hp,autoEquiv i,auto_preserves i,rfl⟩
#print axioms four_support_cover
#check four_support_cover

/-- Exact list identity exhausts every5-subset, rather than enumerating only
a prefiltered list assumed to contain every admissible physical support. -/
theorem five_entries_complete : entries5.reverse.map Prod.fst=(List.finRange 15).sublistsLen 5:=by decide +kernel

theorem all_five_checked : entries5.all (fun entry=>
 decide (ProperFive entry.1.toFinset → entry.1.toFinset.image (autoMap entry.2)∈representatives5))=true:=by decide +kernel

theorem five_support_cover (s:Finset V) (hc:s.card=5) (hp:ProperFive s):
 ∃r∈representatives5,∃e:V≃V,(∀a b,a≠b → T (e a) (e b)=T a b) ∧ s.image e=r:=by
 obtain ⟨xs,hxs,hset⟩:=support_as_sublist s 5 hc
 rw [←five_entries_complete] at hxs
 obtain ⟨⟨ys,i⟩,hy,hys⟩:=List.mem_map.mp hxs
 have hy':(ys,i)∈entries5:=List.mem_reverse.mp hy
 have hh:=of_decide_eq_true ((List.all_eq_true.mp all_five_checked) (ys,i) hy')
 change ys=xs at hys
 subst ys
 rw [hset] at hh
 exact ⟨s.image (autoMap i),hh hp,autoEquiv i,auto_preserves i,rfl⟩
#print axioms five_support_cover
#check five_support_cover

end PricingC.U15SupportCover
