import UniformK60.BalancedEncodingBraces

/-! Evaluation caches for exact ordered brace facts. Row metadata is evaluated
once before its twelve marked choices; no encoded fact or ordering changes. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace UniformK60.BalancedEncodingBraces
open Ramsey61 UniformK60.Physical UniformK60.BalancedProjectedData
open UniformK60.Core (PhysicalUnit)
open CompletionC.NativeMatrices (Shape)

structure RowData where
  kind : Bool
  free : Nat
  right : Nat
  supportCode : Nat
  matrixCode : Nat
  deriving DecidableEq

structure MarkData where
  kind : Bool
  position : Fin 15

/-- Flat lookup copies of the existing finite row metadata. `rowData_eq` checks
all60 entries in the kernel before any serializer uses them. -/
def kindTable : Array Bool := #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]

def shapeTable : Array Shape := #[.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.allFive,.allFive,.allFive,.allFive,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.freeFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.rightFour,.allFive,.allFive,.allFive,.allFive]

def supportCodeTable : Array Nat := #[893456,893456,893456,893456,893456,893456,893456,893456,41488,41488,41488,41488,41488,41488,41488,41488,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,893456,41488,41488,41488,41488,53776,53776,53776,53776,53776,53776,55824,55824,55824,55824,55824,55824,64784,64784,64784,64784,893456,893456,893456,893456]

def matrixCodeTable : Array Nat := #[25718959405063168440896482608737670091166076481848338706343209,25718959513899461529032274708551768942328479552423575937357334,25718959405063168440896482608737840855221929718222700813755689,25718959513899461529032274708551608424823198944326560065787414,25718959334349326210874797779898581608467496419086294619283753,25718959334353985382905330127065582955901375741143406409684502,25718959513911245922952083673078908689325723816193927575527721,25718959447710973688291540256891024913707129064138389523550742,2015155067613227604603936123852008712160131768519550262859926,2015087727588013585103731744613469820309693229257209047177366,2015201109844082127191755719304869342807328918143832578087062,2015008091712760387331583133934629581623326300694704177043606,2015110788353431300904299110431953538102784573642280821625961,2015153518655332563428729633087785251505576433199815017665641,2015182742346256551421029583157728722877462073567136520377449,2015008120156139364732678071109192239130483650936757106869353,413491974067549104728483150126880590472524893574004342181106793,413492419372850920400114991416576442096119563823783458308642966,413491684416981471101896209216129437121640030212744320239371369,413491684493348582864226906916364115050941703406052241542502550,25718959405063168440896482608737670091166076481848338706343209,25718959536341275889511230983607253861016618197947402097534249,25718959517290055305080247224337462181839878030879956232840489,25718959334330692700582061862697803713785317442342243447350569,25718959447716457330006611669593949087536382226549357271983401,25718959405063168440896482608737840855221929718222700813755689,25718959536341275889511230983607237077201234606000364010612009,25718959517290055305080247224337354409453300334302289260455209,25718959334330692700582061862697842637258420040996629594514729,25718959405061801009357423600469594436569117965298411558282537,25718959334349326210874797779898581608467496419086294619283753,25718959447715087172222890006984086652242591562327211911700777,25718959536359911072354752477216481846754013889607631364448553,25718959513911245922952083673078908689325723816193927575527721,25718959452204820202103423767811414764039990988722091232616745,25718959519523409484056812165763488911154981730792053810946345,2015110788353431300904299110431953538102784573642280821625961,2015153518655332563428729633087785251505576433199815017665641,2015182742346256551421029583157728722877462073567136520377449,2015008120156139364732678071109192239130483650936757106869353,433276562529927202935699623979338964736981149872491850667113,433323881340081196494850614018356673438897890099874805879913,433343914545300833482815118038154365820498636078567282218089,433182957599739395518996861174503620142226462529907375248489,433276540119625467964120439468723061011656911166108338787433,433183071344756357728039688265142938780699930591119568634985,26138104599462765524304055198966521335719033573894742945862761,26137890085977141167485258029402224584203711035857583959479401,26138011205488645246180930874059082516982316688699588122023017,26138075426646347688079587322501079405659619950572273083651177,26138104527611692282572387127061638839957749189019537123611753,26138075526951760834976049909475203236774966123393408393643113,27324476755597582761384611412468984433809979339118243161085033,27324335945569374782520223239797376335247775971881826990199913,27324456849608771607101422553176307394411659958420870791730281,27324374266989609344344917294109144150737754261223697147069545,413491974067549104728483150126880590472524893574004342181106793,413492511210340046940944326329475064650689625692459809673090153,413492433547024682747075127028293595043040081370868859797541993,413491684416981471101896209216129437121640030212744320239371369]

def rowData (r : Row) : RowData :=
  let shape := shapeTable[r.val]'(by simpa [shapeTable] using r.isLt)
  ⟨kindTable[r.val]'(by simpa [kindTable] using r.isLt),shape.free,shape.right,
    supportCodeTable[r.val]'(by simpa [supportCodeTable] using r.isLt),
    matrixCodeTable[r.val]'(by simpa [matrixCodeTable] using r.isLt)⟩

set_option maxHeartbeats 0 in
theorem rowData_eq : ∀ r : Row,rowData r=
    ⟨rowKind r,(rowShape r).free,(rowShape r).right,rowRealSupportCode r,rowMatrixCode r⟩ := by
  decide +kernel
def markData (m : MarkChoice) : MarkData := ⟨markedKind m,markedPosition m⟩

def supportUsing (d : RowData) (i : Fin 5) : Fin 16 := digit16 d.supportCode i.val

def matrixUsing (d : RowData) (a b : Fin 15) : Color :=
  if a=b then 0 else
  let index := if a<b then pairIndex a.val b.val else pairIndex b.val a.val
  ⟨((d.matrixCode >>> (2*index)) &&& 3)%4,Nat.mod_lt _ (by decide)⟩

def orderUsing (m : MarkData) (i : Fin 15) : Fin 15 :=
  if h : i.val=14 then m.position else
    if hl : i.val<m.position.val then i else ⟨i.val+1,by omega⟩

def supportVertexUsing (d : RowData) (i : Fin 15) : Vertex :=
  if i.val<d.free then vertex (1+i.val)
  else if i.val<d.free+5 then vertex (15+i.val-d.free)
  else vertex (29+(supportUsing d (supportIndex (i.val-d.free-5))).val)

def braceUsing (d : RowData) (v : Vertex) : Bool :=
  decide (v=0 ∨ (1≤v.val ∧ v.val≤d.free) ∨ (15≤v.val ∧ v.val≤19) ∨
    ∃ j : Fin 5,j.val<d.right ∧ v.val=29+(supportUsing d j).val)

def physicalUsing (d : RowData) (m : MarkData) (v : Vertex) : Vertex :=
  if v.val=0 then 0 else if v.val≤28 then vertex (v.val+31)
  else if v.val≤44 then vertex (16+(cycle d.kind ⟨(v.val-29)%16,Nat.mod_lt _ (by decide)⟩).val)
  else vertex (1+(cycle m.kind (orderUsing m (coord (v.val-45))).castSucc).val)

def rawUsing (d : RowData) (m : MarkData) (r : Row) : List PhysicalUnit :=
  rawRootUnits ++
  ((UniformK60.BalancedEncoding.pairs 16).map fun (a,b) =>
    positiveUnit (vertex (29+a.val)) (vertex (29+b.val))
      (UniformK60.PhysicalHelpers.foreign 2 (R4333.k16Template d.kind a b))) ++
  ((UniformK60.BalancedEncoding.pairs 15).map fun (a,b) =>
    positiveUnit (vertex (45+a.val)) (vertex (45+b.val))
      (UniformK60.PhysicalHelpers.foreign 3
        (R4333.k16Template m.kind (orderUsing m a).castSucc (orderUsing m b).castSucc))) ++
  (((UniformK60.BalancedEncoding.pairs 5).filter fun (_,b) => b.val<d.free).map fun (a,b) =>
    positiveUnit (vertex (1+a.val)) (vertex (1+b.val)) (matrixUsing d (coord a.val) (coord b.val))) ++
  ((UniformK60.BalancedEncoding.pairs 5).map fun (a,b) =>
    positiveUnit (vertex (15+a.val)) (vertex (15+b.val))
      (matrixUsing d (coord (d.free+a.val)) (coord (d.free+b.val)))) ++
  (((crossOrders[r.val]!).toList).map fun code =>
    let a := coord (code%16)
    let b := coord (code/16)
    positiveUnit (supportVertexUsing d a) (supportVertexUsing d b) (matrixUsing d a b)) ++
  (((List.finRange 60).filter fun v => 1≤v.val ∧ v.val<59).map fun v =>
    ⟨braceUsing d v,59,v,3⟩)

theorem physicalUsing_eq (r : Row) (m : MarkChoice) (v : Vertex) :
    physicalUsing (rowData r) (markData m) v=physicalVertex r m v := by
  rw [rowData_eq]
  rfl

theorem rawUsing_eq (r : Row) (m : MarkChoice) :
    rawUsing (rowData r) (markData m) r=rawUnits r m := by
  rw [rowData_eq]
  rfl

def unitsUsing (d : RowData) (m : MarkData) (r : Row) : List PhysicalUnit :=
  let vertices := Array.ofFn (physicalUsing d m)
  (rawUsing d m r).map fun u =>
    ⟨u.positive,vertices[u.u.val]'(by simp [vertices]),
      vertices[u.v.val]'(by simp [vertices]),physicalColor u.q⟩

theorem unitsUsing_eq (r : Row) (m : MarkChoice) :
    unitsUsing (rowData r) (markData m) r=units (r,m) := by
  simp only [unitsUsing,rawUsing_eq,Array.getElem_ofFn,units]
  apply List.map_congr_left
  intro u _
  simp only [physicalUsing_eq]
  rfl

def fastUnits (c : Case) : List PhysicalUnit := unitsUsing (rowData c.1) (markData c.2) c.1

theorem fastUnits_eq (c : Case) : fastUnits c=units c := unitsUsing_eq c.1 c.2

def fastRow (r : Row) : Array (List PhysicalUnit) :=
  let d := rowData r
  Array.ofFn fun m : MarkChoice => unitsUsing d (markData m) r

theorem fastRow_get (r : Row) (m : MarkChoice) :
    (fastRow r)[m.val]'(by simp [fastRow])=units (r,m) := by
  simp only [fastRow,Array.getElem_ofFn,unitsUsing_eq]

#print axioms fastUnits_eq
#print axioms fastRow_get
end UniformK60.BalancedEncodingBraces
