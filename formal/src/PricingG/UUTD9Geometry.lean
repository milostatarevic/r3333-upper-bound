import PricingG.UUTD9Realization
namespace R4333.UUTD9Geometry
open ProfileDTripleJoinReduction ProfileDRowExtension
open ProfileDHighOwnFiveRowSplit61 ProfileDColumnOwnColorIncidence61
open ProfileDUUUFiveSupportPositionSymmetry ProfileDDegreeNineFullNeighborhoodNormalForm61
open ProfileDHighOwnForeignC5Skeleton61
abbrev BlockTwoPosition := Fin (blockSize (2 : Fin 3))
set_option maxHeartbeats 0
theorem degreeNineSkeleton_blockTwo_blockZero_card
    {selected : BlockTwoPosition}
    {branch : PositionedFiveSupport .uut 2 selected}
    (skeleton : DegreeNineSkeleton branch.toSemantic) :
    (foreignOwnSupport branch.toSemantic 0).card =
      if skeleton.firstLarge then 5 else 4 := by
  cases skeleton with
  | mk degree firstLarge freeCycle largeSupport smallSupport =>
      cases firstLarge
      · simpa [smallForeignBlock, firstForeignBlock,
          PositionedFiveSupport.toSemantic] using smallSupport.supportCard
      · simpa [largeForeignBlock, firstForeignBlock,
          PositionedFiveSupport.toSemantic] using largeSupport.supportCard

theorem degreeNineSkeleton_blockTwo_blockOne_card
    {selected : BlockTwoPosition}
    {branch : PositionedFiveSupport .uut 2 selected}
    (skeleton : DegreeNineSkeleton branch.toSemantic) :
    (foreignOwnSupport branch.toSemantic 1).card =
      if skeleton.firstLarge then 4 else 5 := by
  cases skeleton with
  | mk degree firstLarge freeCycle largeSupport smallSupport =>
      cases firstLarge
      · simpa [largeForeignBlock, secondForeignBlock,
          PositionedFiveSupport.toSemantic] using largeSupport.supportCard
      · simpa [smallForeignBlock, secondForeignBlock,
          PositionedFiveSupport.toSemantic] using smallSupport.supportCard



#print axioms degreeNineSkeleton_blockTwo_blockOne_card
end R4333.UUTD9Geometry
