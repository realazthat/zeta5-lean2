import AppendixNumericConstants
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem potential_upper_32 : potential (59205077/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-666756829/100000000 : ℝ) := by
    convert support_log_upper_0 using 1 <;> norm_num [componentPotential]
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (59205077/10000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_33 : potential (59205079/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-666756829/100000000 : ℝ) := by
    convert support_log_upper_0 using 1 <;> norm_num [componentPotential]
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (59205079/10000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_34 : potential (8992695531/1000000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-666756829/100000000 : ℝ) := by
    convert support_log_upper_0 using 1 <;> norm_num [componentPotential]
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (8992695531/1000000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_35 : potential (19572466643/2000000000000 : ℝ) ≤ (-35752570333635776921/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-589678909/100000000 : ℝ) := by
    have heq : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) = Real.log (((3336511513/1000000000000 : ℝ) + Real.sqrt (18662374892224168651/4000000000000000000000000 : ℝ))/2) := by norm_num [componentPotential]
    rw [heq]
    apply log_sqrt_upper (u := (53999963675080619/25000000000000000000 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    ·
      convert Zeta5LogCertificates.log_le_of_check (137412751500080619/50000000000000000000 : ℚ) (-589678909/100000000 : ℚ)
        [(15844121990012270429471/302231454903657293676544 : ℚ),
         (69199653472488128984337/302231454903657293676544 : ℚ),
         (144617813383479864454603/302231454903657293676544 : ℚ),
         (209064708030491652547217/302231454903657293676544 : ℚ),
         (502736236517972978097585/604462909807314587353088 : ℚ),
         (1102516046851441114127737/1208925819614629174706176 : ℚ),
         (577247805448006737635175/604462909807314587353088 : ℚ),
         (1181397288232859919557789/1208925819614629174706176 : ℚ),
         (1195082292131973011115847/1208925819614629174706176 : ℚ),
         (1201984126152494233291109/1208925819614629174706176 : ℚ),
         (1205449976097174229539253/1208925819614629174706176 : ℚ),
         (1207186646860257273857211/1208925819614629174706176 : ℚ),
         (604027960131683895012743/604462909807314587353088 : ℚ),
         (604245395833658176192063/604462909807314587353088 : ℚ),
         (604354143034765356683369/604462909807314587353088 : ℚ),
         (1208817047948779172465537/1208925819614629174706176 : ℚ),
         (604435716279161971991003/604462909807314587353088 : ℚ),
         (604449312890312311041709/604462909807314587353088 : ℚ),
         (1208912222621163054080239/1208925819614629174706176 : ℚ),
         (1208919021098780045813587/1208925819614629174706176 : ℚ),
         (151115302543990697459661/151115727451828646838272 : ℚ),
         (1208924119982082617866369/1208925819614629174706176 : ℚ),
         (1208924969798057206244967/1208925819614629174706176 : ℚ),
         (151115674338283564742375/151115727451828646838272 : ℚ),
         (1208925607160430178185165/1208925819614629174706176 : ℚ),
         (1208925713387525009410905/1208925819614629174706176 : ℚ),
         (604462883250537962649899/604462909807314587353088 : ℚ),
         (1208925793057852258313295/1208925819614629174706176 : ℚ),
         (75557862896015040224207/75557863725914323419136 : ℚ),
         (604462906487717445458069/604462909807314587353088 : ℚ),
         (604462908147516014126753/604462909807314587353088 : ℚ),
         (1208925817954830600340429/1208925819614629174706176 : ℚ),
         (604462909392364943619225/604462909807314587353088 : ℚ),
         (302231454799919882725275/302231454903657293676544 : ℚ)] (by decide +kernel) using 1 <;> norm_num
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (19572466643/2000000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_36 : potential (40732008867/4000000000000 : ℝ) ≤ (-35731207021943825891/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-573426241/100000000 : ℝ) := by
    have heq : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) = Real.log (((14933121633/4000000000000 : ℝ) + Real.sqrt (119530676052764474589/16000000000000000000000000 : ℝ))/2) := by norm_num [componentPotential]
    rw [heq]
    apply log_sqrt_upper (u := (136662606931246739/50000000000000000000 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    ·
      convert Zeta5LogCertificates.log_le_of_check (323326627343746739/100000000000000000000 : ℚ) (-573426241/100000000 : ℚ)
        [(34370859578120989483903/604462909807314587353088 : ℚ),
         (144138509056981793017691/604462909807314587353088 : ℚ),
         (73792946224500000617493/151115727451828646838272 : ℚ),
         (844796770809320358396873/1208925819614629174706176 : ℚ),
         (505296108375685407164449/604462909807314587353088 : ℚ),
         (276329855418790653567983/302231454903657293676544 : ℚ),
         (144495306356762301114231/151115727451828646838272 : ℚ),
         (591073779942598709007481/604462909807314587353088 : ℚ),
         (597730856602628097429803/604462909807314587353088 : ℚ),
         (1202174917162462305653503/1208925819614629174706176 : ℚ),
         (1205545642873291909483831/1208925819614629174706176 : ℚ),
         (1207234548210677848495547/1208925819614629174706176 : ℚ),
         (604039943973635380266005/604462909807314587353088 : ℚ),
         (604251389881852832279633/604462909807314587353088 : ℚ),
         (1208714281181618025461863/1208925819614629174706176 : ℚ),
         (1208820045770831399755905/1208925819614629174706176 : ℚ),
         (1208872931535856626801287/1208925819614629174706176 : ℚ),
         (1208899375286018159110653/1208925819614629174706176 : ℚ),
         (604456298689008345332777/604462909807314587353088 : ℚ),
         (1208919208478246089770193/1208925819614629174706176 : ℚ),
         (604461257020959204576169/604462909807314587353088 : ℚ),
         (151115520853392998076647/151115727451828646838272 : ℚ),
         (604462496610302063818789/604462909807314587353088 : ℚ),
         (604462703208773019071109/604462909807314587353088 : ℚ),
         (604462806508034976581883/604462909807314587353088 : ℚ),
         (604462858157672575309743/604462909807314587353088 : ℚ),
         (1208925767964986059333913/1208925819614629174706176 : ℚ),
         (604462896894903670593905/604462909807314587353088 : ℚ),
         (604462903351109094494467/604462909807314587353088 : ℚ),
         (1208925813158423664608041/1208925819614629174706176 : ℚ),
         (604462908193263207673615/604462909807314587353088 : ℚ),
         (604462909000288896974617/604462909807314587353088 : ℚ),
         (604462909403801742029169/604462909807314587353088 : ℚ),
         (302231454802779082328729/302231454903657293676544 : ℚ)] (by decide +kernel) using 1 <;> norm_num
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (40732008867/4000000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_37 : potential (1322471389/125000000000 : ℝ) ≤ (-71427521894559220797/25000000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-140038427/25000000 : ℝ) := by
    have heq : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) = Real.log (((8260098607/2000000000000 : ℝ) + Real.sqrt (5295295948007664053/500000000000000000000000 : ℝ))/2) := by norm_num [componentPotential]
    rw [heq]
    apply log_sqrt_upper (u := (81357974009986139/25000000000000000000 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    ·
      convert Zeta5LogCertificates.log_le_of_check (184609206597486139/50000000000000000000 : ℚ) (-140038427/25000000 : ℚ)
        [(18364594254590302458181/302231454903657293676544 : ℚ),
         (298002900396091388909335/1208925819614629174706176 : ℚ),
         (75027432546461118918113/151115727451828646838272 : ℚ),
         (425916894205458379082245/604462909807314587353088 : ℚ),
         (507396260537585689833099/604462909807314587353088 : ℚ),
         (553807024215023253810747/604462909807314587353088 : ℚ),
         (578580854616485634995129/604462909807314587353088 : ℚ),
         (591380306520502718524795/604462909807314587353088 : ℚ),
         (1195771651917078505064827/1208925819614629174706176 : ℚ),
         (601165373330374292645145/604462909807314587353088 : ℚ),
         (1205623773552394143883547/1208925819614629174706176 : ℚ),
         (75454604227804741167429/75557863725914323419136 : ℚ),
         (302024865300518444602107/302231454903657293676544 : ℚ),
         (604256284888644940162443/604462909807314587353088 : ℚ),
         (604359588517587743326421/604462909807314587353088 : ℚ),
         (604411246954664466897931/604462909807314587353088 : ℚ),
         (302218538914509632042127/302231454903657293676544 : ℚ),
         (604449993680171411294247/604462909807314587353088 : ℚ),
         (1208912903418487504255313/1208925819614629174706176 : ℚ),
         (604459680749654311867201/604462909807314587353088 : ℚ),
         (302230647638164114691277/302231454903657293676544 : ℚ),
         (1208924205082564705182019/1208925819614629174706176 : ℚ),
         (1208925012348327411875713/1208925819614629174706176 : ℚ),
         (151115676997676363906419/151115727451828646838272 : ℚ),
         (604462808899001598733027/604462909807314587353088 : ℚ),
         (604462859353155987353793/604462909807314587353088 : ℚ),
         (1208925769160469521862205/1208925819614629174706176 : ℚ),
         (151115724298443635634127/151115727451828646838272 : ℚ),
         (604462903500544532043401/604462909807314587353088 : ℚ),
         (1208925813307859102945791/1208925819614629174706176 : ℚ),
         (1208925816461244134713309/1208925819614629174706176 : ℚ),
         (604462909018968326840787/604462909807314587353088 : ℚ),
         (1208925818826282913936833/1208925819614629174706176 : ℚ),
         (302231454805114011064311/302231454903657293676544 : ℚ)] (by decide +kernel) using 1 <;> norm_num
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (1322471389/125000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_38 : potential (4549323561/400000000000 : ℝ) ≤ (-71371459507771400717/25000000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-134707071/25000000 : ℝ) := by
    have heq : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) = Real.log (((2461793547/500000000000 : ℝ) + Real.sqrt (71099978075511431319/4000000000000000000000000 : ℝ))/2) := by norm_num [componentPotential]
    rw [heq]
    apply log_sqrt_upper (u := (421604014673459411/100000000000000000000 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    ·
      convert Zeta5LogCertificates.log_le_of_check (913962724073459411/200000000000000000000 : ℚ) (-134707071/25000000 : ℚ)
        [(40861932432472726392513/604462909807314587353088 : ℚ),
         (157160817567491498394617/604462909807314587353088 : ℚ),
         (616434538599330709289859/1208925819614629174706176 : ℚ),
         (431631680317536945474109/604462909807314587353088 : ℚ),
         (63848617527339493883287/75557863725914323419136 : ℚ),
         (555655440990187283636563/604462909807314587353088 : ℚ),
         (1159091203851008764914597/1208925819614629174706176 : ℚ),
         (1183746291915496559428949/1208925819614629174706176 : ℚ),
         (149533726137790973266883/151115727451828646838272 : ℚ),
         (1202581165430952356537427/1208925819614629174706176 : ℚ),
         (602874659666445516709471/604462909807314587353088 : ℚ),
         (301834131200844371064977/302231454903657293676544 : ℚ),
         (604065455434798305549809/604462909807314587353088 : ℚ),
         (604264149942886234013921/604462909807314587353088 : ℚ),
         (4721590013314175191251/4722366482869645213696 : ℚ),
         (75551651714109382008241/75557863725914323419136 : ℚ),
         (1208876122498702927147959/1208925819614629174706176 : ℚ),
         (151112621350161140344035/151115727451828646838272 : ℚ),
         (1208913395144114260535353/1208925819614629174706176 : ℚ),
         (604459803681705206776393/604462909807314587353088 : ℚ),
         (604461356742514728930001/604462909807314587353088 : ℚ),
         (302231066637207932733539/302231454903657293676544 : ℚ),
         (604462521540740528161369/604462909807314587353088 : ℚ),
         (302231357836998191592519/302231454903657293676544 : ℚ),
         (151115703185161922906191/151115727451828646838272 : ℚ),
         (604462861273979191077695/604462909807314587353088 : ℚ),
         (1208925771081292804225129/1208925819614629174706176 : ℚ),
         (604462897673980372957117/604462909807314587353088 : ℚ),
         (604462903740647449711175/604462909807314587353088 : ℚ),
         (302231453386990505460575/302231454903657293676544 : ℚ),
         (302231454145323898617187/302231454903657293676544 : ℚ),
         (604462909048981191818045/604462909807314587353088 : ℚ),
         (604462909428147889466645/604462909807314587353088 : ℚ),
         (1208925819235462476760273/1208925819614629174706176 : ℚ)] (by decide +kernel) using 1 <;> norm_num
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (4549323561/400000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

theorem potential_upper_39 : potential (12166846693/1000000000000 : ℝ) ≤ (-35663331824515644831/12500000000000000000 : ℝ) := by
  have h0 : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-104357701/20000000 : ℝ) := by
    have heq : componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) = Real.log (((11434249769/2000000000000 : ℝ) + Real.sqrt (13109400795821815667/500000000000000000000000 : ℝ))/2) := by norm_num [componentPotential]
    rw [heq]
    apply log_sqrt_upper (u := (512042982489201109/100000000000000000000 : ℝ))
    · norm_num
    · norm_num
    · norm_num
    ·
      convert Zeta5LogCertificates.log_le_of_check (1083755470939201109/200000000000000000000 : ℚ) (-104357701/20000000 : ℚ)
        [(88991864663124297190863/1208925819614629174706176 : ℚ),
         (164000429059577231654319/604462909807314587353088 : ℚ),
         (629705253460696884689441/1208925819614629174706176 : ℚ),
         (436253062927817959485531/604462909807314587353088 : ℚ),
         (1027032221168746705825195/1208925819614629174706176 : ℚ),
         (69642103199676946323095/75557863725914323419136 : ℚ),
         (1160635251509145167811449/1208925819614629174706176 : ℚ),
         (296133618775410717757495/302231454903657293676544 : ℚ),
         (1196668003739566090579765/1208925819614629174706176 : ℚ),
         (300695324126791280976705/302231454903657293676544 : ℚ),
         (602924822158009785901559/604462909807314587353088 : ℚ),
         (150923344035285065149951/151115727451828646838272 : ℚ),
         (1208156040871667049160971/1208925819614629174706176 : ℚ),
         (151067608619304617027881/151115727451828646838272 : ℚ),
         (1208733328959915303489511/1208925819614629174706176 : ℚ),
         (604414785227906381925371/604462909807314587353088 : ℚ),
         (604438847038658984076807/604462909807314587353088 : ℚ),
         (1208901756606493054443515/1208925819614629174706176 : ℚ),
         (1208913788050690389479727/1208925819614629174706176 : ℚ),
         (604459901908846013168729/604462909807314587353088 : ℚ),
         (1208922811712418652272689/1208925819614629174706176 : ℚ),
         (1208924315662588425263367/1208925819614629174706176 : ℚ),
         (604462533819187463891391/604462909807314587353088 : ℚ),
         (604462721813221791587899/604462909807314587353088 : ℚ),
         (151115703952565220240193/151115727451828646838272 : ℚ),
         (302231431404392953514679/302231454903657293676544 : ℚ),
         (1208925772616099580818625/1208925819614629174706176 : ℚ),
         (1208925796115364149371441/1208925819614629174706176 : ℚ),
         (302231451966249151235267/302231454903657293676544 : ℚ),
         (1208925813739812875549187/1208925819614629174706176 : ℚ),
         (1208925816677221021559073/1208925819614629174706176 : ℚ),
         (1208925818145925097240473/1208925819614629174706176 : ℚ),
         (1208925818880277135750287/1208925819614629174706176 : ℚ),
         (151115727405931644396559/151115727451828646838272 : ℚ)] (by decide +kernel) using 1 <;> norm_num
  have h1 : componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
    convert support_log_upper_1 using 1 <;> norm_num [componentPotential]
  have h2 : componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
    convert support_log_upper_2 using 1 <;> norm_num [componentPotential]
  have h3 : componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
    convert support_log_upper_3 using 1 <;> norm_num [componentPotential]
  have h4 : componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
    convert support_log_upper_4 using 1 <;> norm_num [componentPotential]
  have h5 : componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
    convert support_log_upper_5 using 1 <;> norm_num [componentPotential]
  have h6 : componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
    convert support_log_upper_6 using 1 <;> norm_num [componentPotential]
  have h7 : componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
    convert support_log_upper_7 using 1 <;> norm_num [componentPotential]
  have h8 : componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
    convert support_log_upper_8 using 1 <;> norm_num [componentPotential]
  have h9 : componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
    convert support_log_upper_9 using 1 <;> norm_num [componentPotential]
  have h10 : componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
    convert support_log_upper_10 using 1 <;> norm_num [componentPotential]
  have h11 : componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
    convert support_log_upper_11 using 1 <;> norm_num [componentPotential]
  have h12 : componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
    convert support_log_upper_12 using 1 <;> norm_num [componentPotential]
  have h13 : componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
    convert support_log_upper_13 using 1 <;> norm_num [componentPotential]
  have h14 : componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
    convert support_log_upper_14 using 1 <;> norm_num [componentPotential]
  have h15 : componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) (12166846693/1000000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
    convert support_log_upper_15 using 1 <;> norm_num [componentPotential]
  have hsum := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ (525779809/50000000000 : ℝ))) (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ (29471737793/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ (42934365099/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ (29102115983/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (6903762131/100000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ (78873099189/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ (84856120711/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (88396082127/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ (706427057/8000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h9 (by norm_num : (0 : ℝ) ≤ (17094464251/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h10 (by norm_num : (0 : ℝ) ≤ (39449592119/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h11 (by norm_num : (0 : ℝ) ≤ (35176735959/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ (11767795323/200000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ (22210660553/500000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h14 (by norm_num : (0 : ℝ) ≤ (30462865791/1000000000000 : ℝ)))) (mul_le_mul_of_nonneg_left h15 (by norm_num : (0 : ℝ) ≤ (5959622577/1000000000000 : ℝ))))
  norm_num only [potential] at hsum ⊢
  exact hsum

#print axioms potential_upper_39
end Zeta5AppendixNumerics
