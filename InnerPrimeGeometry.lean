import InnerPrimeCells
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace Zeta5InnerAsymptotics

theorem innerCell_bounds (i : Fin 143) :
    3≤ innerCellLeft i ∧ innerCellLeft i≤ innerCellRight i ∧ innerCellRight i≤20 := by
  fin_cases i <;> norm_num [innerCellLeft,innerCellRight]

end Zeta5InnerAsymptotics
