import PricingABD.Schedules.BUUU4Chunk00
import PricingABD.Schedules.BUUU4Chunk01
import PricingABD.Schedules.BUUU4Chunk02
import PricingABD.Schedules.BUUU4Chunk03
import PricingABD.Schedules.BUUU4Chunk04
import PricingABD.Schedules.BUUU4Chunk05
import PricingABD.Schedules.BUUU4Chunk06
import PricingABD.Schedules.BUUU4Chunk07
import PricingABD.Schedules.BUUU4Chunk08
import PricingABD.Schedules.BUUU4Chunk09
import PricingABD.Schedules.BUUU4Chunk10
import PricingABD.Schedules.BUUU4Chunk11
import PricingABD.Schedules.BUUU4Chunk12
import PricingABD.Schedules.BUUU4Chunk13
import PricingABD.Schedules.BUUU4Chunk14
import PricingABD.Schedules.BUUU4Chunk15
namespace PricingABD.Schedules.BUUU4Complete
open Ramsey61 Ramsey61.DenseCounter PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABProgram PricingABD.Schedules.BUUU4
open PricingIntegration.NativePrimary
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
 theorem fold_all : ∀i:Fin 488,FoldOK program types i := by
  intro i
  by_cases h0:i.val<32
  ·
    let j:Fin 32:=⟨i.val-0,by omega⟩
    have he:(⟨0+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
    simpa only [he] using PricingABD.Schedules.BUUU4Chunk00.fold j
  ·
    by_cases h1:i.val<64
    ·
      let j:Fin 32:=⟨i.val-32,by omega⟩
      have he:(⟨32+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
      simpa only [he] using PricingABD.Schedules.BUUU4Chunk01.fold j
    ·
      by_cases h2:i.val<96
      ·
        let j:Fin 32:=⟨i.val-64,by omega⟩
        have he:(⟨64+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
        simpa only [he] using PricingABD.Schedules.BUUU4Chunk02.fold j
      ·
        by_cases h3:i.val<128
        ·
          let j:Fin 32:=⟨i.val-96,by omega⟩
          have he:(⟨96+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
          simpa only [he] using PricingABD.Schedules.BUUU4Chunk03.fold j
        ·
          by_cases h4:i.val<160
          ·
            let j:Fin 32:=⟨i.val-128,by omega⟩
            have he:(⟨128+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
            simpa only [he] using PricingABD.Schedules.BUUU4Chunk04.fold j
          ·
            by_cases h5:i.val<192
            ·
              let j:Fin 32:=⟨i.val-160,by omega⟩
              have he:(⟨160+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
              simpa only [he] using PricingABD.Schedules.BUUU4Chunk05.fold j
            ·
              by_cases h6:i.val<224
              ·
                let j:Fin 32:=⟨i.val-192,by omega⟩
                have he:(⟨192+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                simpa only [he] using PricingABD.Schedules.BUUU4Chunk06.fold j
              ·
                by_cases h7:i.val<256
                ·
                  let j:Fin 32:=⟨i.val-224,by omega⟩
                  have he:(⟨224+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                  simpa only [he] using PricingABD.Schedules.BUUU4Chunk07.fold j
                ·
                  by_cases h8:i.val<288
                  ·
                    let j:Fin 32:=⟨i.val-256,by omega⟩
                    have he:(⟨256+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                    simpa only [he] using PricingABD.Schedules.BUUU4Chunk08.fold j
                  ·
                    by_cases h9:i.val<320
                    ·
                      let j:Fin 32:=⟨i.val-288,by omega⟩
                      have he:(⟨288+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                      simpa only [he] using PricingABD.Schedules.BUUU4Chunk09.fold j
                    ·
                      by_cases h10:i.val<352
                      ·
                        let j:Fin 32:=⟨i.val-320,by omega⟩
                        have he:(⟨320+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                        simpa only [he] using PricingABD.Schedules.BUUU4Chunk10.fold j
                      ·
                        by_cases h11:i.val<384
                        ·
                          let j:Fin 32:=⟨i.val-352,by omega⟩
                          have he:(⟨352+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                          simpa only [he] using PricingABD.Schedules.BUUU4Chunk11.fold j
                        ·
                          by_cases h12:i.val<416
                          ·
                            let j:Fin 32:=⟨i.val-384,by omega⟩
                            have he:(⟨384+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                            simpa only [he] using PricingABD.Schedules.BUUU4Chunk12.fold j
                          ·
                            by_cases h13:i.val<448
                            ·
                              let j:Fin 32:=⟨i.val-416,by omega⟩
                              have he:(⟨416+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                              simpa only [he] using PricingABD.Schedules.BUUU4Chunk13.fold j
                            ·
                              by_cases h14:i.val<480
                              ·
                                let j:Fin 32:=⟨i.val-448,by omega⟩
                                have he:(⟨448+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                                simpa only [he] using PricingABD.Schedules.BUUU4Chunk14.fold j
                              ·
                                let j:Fin 8:=⟨i.val-480,by omega⟩
                                have he:(⟨480+j.val,by have hh:=j.isLt;omega⟩:Fin 488)=i := by apply Fin.ext;dsimp [j];omega
                                simpa only [he] using PricingABD.Schedules.BUUU4Chunk15.fold j
 theorem input_all : ∀i:Fin 433,InputOK program i := by
  intro i
  by_cases h0:i.val<32
  ·
    let j:Fin 32:=⟨i.val-0,by omega⟩
    have he:(⟨0+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
    simpa only [he] using PricingABD.Schedules.BUUU4Chunk00.input j
  ·
    by_cases h1:i.val<64
    ·
      let j:Fin 32:=⟨i.val-32,by omega⟩
      have he:(⟨32+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
      simpa only [he] using PricingABD.Schedules.BUUU4Chunk01.input j
    ·
      by_cases h2:i.val<96
      ·
        let j:Fin 32:=⟨i.val-64,by omega⟩
        have he:(⟨64+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
        simpa only [he] using PricingABD.Schedules.BUUU4Chunk02.input j
      ·
        by_cases h3:i.val<128
        ·
          let j:Fin 32:=⟨i.val-96,by omega⟩
          have he:(⟨96+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
          simpa only [he] using PricingABD.Schedules.BUUU4Chunk03.input j
        ·
          by_cases h4:i.val<160
          ·
            let j:Fin 32:=⟨i.val-128,by omega⟩
            have he:(⟨128+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
            simpa only [he] using PricingABD.Schedules.BUUU4Chunk04.input j
          ·
            by_cases h5:i.val<192
            ·
              let j:Fin 32:=⟨i.val-160,by omega⟩
              have he:(⟨160+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
              simpa only [he] using PricingABD.Schedules.BUUU4Chunk05.input j
            ·
              by_cases h6:i.val<224
              ·
                let j:Fin 32:=⟨i.val-192,by omega⟩
                have he:(⟨192+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                simpa only [he] using PricingABD.Schedules.BUUU4Chunk06.input j
              ·
                by_cases h7:i.val<256
                ·
                  let j:Fin 32:=⟨i.val-224,by omega⟩
                  have he:(⟨224+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                  simpa only [he] using PricingABD.Schedules.BUUU4Chunk07.input j
                ·
                  by_cases h8:i.val<288
                  ·
                    let j:Fin 32:=⟨i.val-256,by omega⟩
                    have he:(⟨256+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                    simpa only [he] using PricingABD.Schedules.BUUU4Chunk08.input j
                  ·
                    by_cases h9:i.val<320
                    ·
                      let j:Fin 32:=⟨i.val-288,by omega⟩
                      have he:(⟨288+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                      simpa only [he] using PricingABD.Schedules.BUUU4Chunk09.input j
                    ·
                      by_cases h10:i.val<352
                      ·
                        let j:Fin 32:=⟨i.val-320,by omega⟩
                        have he:(⟨320+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                        simpa only [he] using PricingABD.Schedules.BUUU4Chunk10.input j
                      ·
                        by_cases h11:i.val<384
                        ·
                          let j:Fin 32:=⟨i.val-352,by omega⟩
                          have he:(⟨352+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                          simpa only [he] using PricingABD.Schedules.BUUU4Chunk11.input j
                        ·
                          by_cases h12:i.val<416
                          ·
                            let j:Fin 32:=⟨i.val-384,by omega⟩
                            have he:(⟨384+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                            simpa only [he] using PricingABD.Schedules.BUUU4Chunk12.input j
                          ·
                            let j:Fin 17:=⟨i.val-416,by omega⟩
                            have he:(⟨416+j.val,by have hh:=j.isLt;omega⟩:Fin 433)=i := by apply Fin.ext;dsimp [j];omega
                            simpa only [he] using PricingABD.Schedules.BUUU4Chunk13.input j
def Adjacent (i:Fin 432) : Prop := actualStart i.succ=actualStart i.castSucc+PricingIntegration.SparseCounter.offset (height i.castSucc) (inputs i.castSucc).length
 theorem adjacent_all : ∀i:Fin 432,Adjacent i := by
  intro i
  by_cases h0:i.val<32
  ·
    let j:Fin 32:=⟨i.val-0,by omega⟩
    have he:(⟨0+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
    have hj:Adjacent (⟨0+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk00.adjacent j
    simpa only [he] using hj
  ·
    by_cases h1:i.val<64
    ·
      let j:Fin 32:=⟨i.val-32,by omega⟩
      have he:(⟨32+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
      have hj:Adjacent (⟨32+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk01.adjacent j
      simpa only [he] using hj
    ·
      by_cases h2:i.val<96
      ·
        let j:Fin 32:=⟨i.val-64,by omega⟩
        have he:(⟨64+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
        have hj:Adjacent (⟨64+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk02.adjacent j
        simpa only [he] using hj
      ·
        by_cases h3:i.val<128
        ·
          let j:Fin 32:=⟨i.val-96,by omega⟩
          have he:(⟨96+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
          have hj:Adjacent (⟨96+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk03.adjacent j
          simpa only [he] using hj
        ·
          by_cases h4:i.val<160
          ·
            let j:Fin 32:=⟨i.val-128,by omega⟩
            have he:(⟨128+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
            have hj:Adjacent (⟨128+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk04.adjacent j
            simpa only [he] using hj
          ·
            by_cases h5:i.val<192
            ·
              let j:Fin 32:=⟨i.val-160,by omega⟩
              have he:(⟨160+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
              have hj:Adjacent (⟨160+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk05.adjacent j
              simpa only [he] using hj
            ·
              by_cases h6:i.val<224
              ·
                let j:Fin 32:=⟨i.val-192,by omega⟩
                have he:(⟨192+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                have hj:Adjacent (⟨192+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk06.adjacent j
                simpa only [he] using hj
              ·
                by_cases h7:i.val<256
                ·
                  let j:Fin 32:=⟨i.val-224,by omega⟩
                  have he:(⟨224+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                  have hj:Adjacent (⟨224+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk07.adjacent j
                  simpa only [he] using hj
                ·
                  by_cases h8:i.val<288
                  ·
                    let j:Fin 32:=⟨i.val-256,by omega⟩
                    have he:(⟨256+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                    have hj:Adjacent (⟨256+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk08.adjacent j
                    simpa only [he] using hj
                  ·
                    by_cases h9:i.val<320
                    ·
                      let j:Fin 32:=⟨i.val-288,by omega⟩
                      have he:(⟨288+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                      have hj:Adjacent (⟨288+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk09.adjacent j
                      simpa only [he] using hj
                    ·
                      by_cases h10:i.val<352
                      ·
                        let j:Fin 32:=⟨i.val-320,by omega⟩
                        have he:(⟨320+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                        have hj:Adjacent (⟨320+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk10.adjacent j
                        simpa only [he] using hj
                      ·
                        by_cases h11:i.val<384
                        ·
                          let j:Fin 32:=⟨i.val-352,by omega⟩
                          have he:(⟨352+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                          have hj:Adjacent (⟨352+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk11.adjacent j
                          simpa only [he] using hj
                        ·
                          by_cases h12:i.val<416
                          ·
                            let j:Fin 32:=⟨i.val-384,by omega⟩
                            have he:(⟨384+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                            have hj:Adjacent (⟨384+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk12.adjacent j
                            simpa only [he] using hj
                          ·
                            let j:Fin 16:=⟨i.val-416,by omega⟩
                            have he:(⟨416+j.val,by have hh:=j.isLt;omega⟩:Fin 432)=i := by apply Fin.ext;dsimp [j];omega
                            have hj:Adjacent (⟨416+j.val,by have hh:=j.isLt;omega⟩) := PricingABD.Schedules.BUUU4Chunk13.adjacent j
                            simpa only [he] using hj
 theorem starts_all : ∀j,actualStart j=PricingIntegration.MultiSparseCounter.start (primaryLimit layout)
     (PricingIntegration.MultiSparseCounter.size inputs height) j := by
  exact PricingIntegration.MultiSparseCounter.starts_eq_of_adjacent (N:=432) _ _ _ (by decide +kernel) adjacent_all
 theorem native_program {c : Host} (t:Types) (hs:PricingABD.ABScheduleTypes.SameSchedule layout t types)
     (f:Frame c layout) (hc:NoMonochromaticTriangle c) (hg:Geometry t f) :
     ∃w:Valuation,(∀a<primaryLimit layout,w a=primary f a) ∧ FormulaSat w (formula program) :=
   satisfying_extension program types t hs fold_all input_all starts_all f hc hg
#print axioms native_program
end PricingABD.Schedules.BUUU4Complete
