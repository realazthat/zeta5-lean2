import AppendixPartition
import AppendixNumerics
import AppendixCells.Batch000
import AppendixCells.Batch001
import AppendixCells.Batch002
import AppendixCells.Batch003
import AppendixCells.Batch004
import AppendixCells.Batch005
import AppendixCells.Batch006
import AppendixCells.Batch007
import AppendixCells.Batch008
import AppendixCells.Batch009
import AppendixCells.Batch010
import AppendixCells.Batch011
import AppendixCells.Batch012
import AppendixCells.Batch013
import AppendixCells.Batch014
import AppendixCells.Batch015
import AppendixCells.Batch016
import AppendixCells.Batch017
import AppendixCells.Batch018
import AppendixCells.Batch019
import AppendixCells.Batch020
import AppendixCells.Batch021
import AppendixCells.Batch022
import AppendixCells.Batch023
import AppendixCells.Batch024
import AppendixCells.Batch025
import AppendixCells.Batch026
import AppendixCells.Batch027
import AppendixCells.Batch028
import AppendixCells.Batch029
import AppendixCells.Batch030
import AppendixCells.Batch031
import AppendixCells.Batch032
import AppendixCells.Batch033
import AppendixCells.Batch034
import AppendixCells.Batch035
import AppendixCells.Batch036
import AppendixCells.Batch037
import AppendixCells.Batch038
import AppendixCells.Batch039
import AppendixCells.Batch040
import AppendixCells.Batch041
import AppendixCells.Batch042
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem all_cell_bounds : ∀ c ∈ cells,
    cellBound (c.1 : ℝ) (c.2 : ℝ) < -6645002/1000000 := by
  exact List.forall_iff_forall_mem.mp ⟨cell_bound_0, ⟨cell_bound_1, ⟨cell_bound_2, ⟨cell_bound_3, ⟨cell_bound_4, ⟨cell_bound_5, ⟨cell_bound_6, ⟨cell_bound_7, ⟨cell_bound_8, ⟨cell_bound_9, ⟨cell_bound_10, ⟨cell_bound_11, ⟨cell_bound_12, ⟨cell_bound_13, ⟨cell_bound_14, ⟨cell_bound_15, ⟨cell_bound_16, ⟨cell_bound_17, ⟨cell_bound_18, ⟨cell_bound_19, ⟨cell_bound_20, ⟨cell_bound_21, ⟨cell_bound_22, ⟨cell_bound_23, ⟨cell_bound_24, ⟨cell_bound_25, ⟨cell_bound_26, ⟨cell_bound_27, ⟨cell_bound_28, ⟨cell_bound_29, ⟨cell_bound_30, ⟨cell_bound_31, ⟨cell_bound_32, ⟨cell_bound_33, ⟨cell_bound_34, ⟨cell_bound_35, ⟨cell_bound_36, ⟨cell_bound_37, ⟨cell_bound_38, ⟨cell_bound_39, ⟨cell_bound_40, ⟨cell_bound_41, ⟨cell_bound_42, ⟨cell_bound_43, ⟨cell_bound_44, ⟨cell_bound_45, ⟨cell_bound_46, ⟨cell_bound_47, ⟨cell_bound_48, ⟨cell_bound_49, ⟨cell_bound_50, ⟨cell_bound_51, ⟨cell_bound_52, ⟨cell_bound_53, ⟨cell_bound_54, ⟨cell_bound_55, ⟨cell_bound_56, ⟨cell_bound_57, ⟨cell_bound_58, ⟨cell_bound_59, ⟨cell_bound_60, ⟨cell_bound_61, ⟨cell_bound_62, ⟨cell_bound_63, ⟨cell_bound_64, ⟨cell_bound_65, ⟨cell_bound_66, ⟨cell_bound_67, ⟨cell_bound_68, ⟨cell_bound_69, ⟨cell_bound_70, ⟨cell_bound_71, ⟨cell_bound_72, ⟨cell_bound_73, ⟨cell_bound_74, ⟨cell_bound_75, ⟨cell_bound_76, ⟨cell_bound_77, ⟨cell_bound_78, ⟨cell_bound_79, ⟨cell_bound_80, ⟨cell_bound_81, ⟨cell_bound_82, ⟨cell_bound_83, ⟨cell_bound_84, ⟨cell_bound_85, ⟨cell_bound_86, ⟨cell_bound_87, ⟨cell_bound_88, ⟨cell_bound_89, ⟨cell_bound_90, ⟨cell_bound_91, ⟨cell_bound_92, ⟨cell_bound_93, ⟨cell_bound_94, ⟨cell_bound_95, ⟨cell_bound_96, ⟨cell_bound_97, ⟨cell_bound_98, ⟨cell_bound_99, ⟨cell_bound_100, ⟨cell_bound_101, ⟨cell_bound_102, ⟨cell_bound_103, ⟨cell_bound_104, ⟨cell_bound_105, ⟨cell_bound_106, ⟨cell_bound_107, ⟨cell_bound_108, ⟨cell_bound_109, ⟨cell_bound_110, ⟨cell_bound_111, ⟨cell_bound_112, ⟨cell_bound_113, ⟨cell_bound_114, ⟨cell_bound_115, ⟨cell_bound_116, ⟨cell_bound_117, ⟨cell_bound_118, ⟨cell_bound_119, ⟨cell_bound_120, ⟨cell_bound_121, ⟨cell_bound_122, ⟨cell_bound_123, ⟨cell_bound_124, ⟨cell_bound_125, ⟨cell_bound_126, ⟨cell_bound_127, ⟨cell_bound_128, ⟨cell_bound_129, ⟨cell_bound_130, ⟨cell_bound_131, ⟨cell_bound_132, ⟨cell_bound_133, ⟨cell_bound_134, ⟨cell_bound_135, ⟨cell_bound_136, ⟨cell_bound_137, ⟨cell_bound_138, ⟨cell_bound_139, ⟨cell_bound_140, ⟨cell_bound_141, ⟨cell_bound_142, ⟨cell_bound_143, ⟨cell_bound_144, ⟨cell_bound_145, ⟨cell_bound_146, ⟨cell_bound_147, ⟨cell_bound_148, ⟨cell_bound_149, ⟨cell_bound_150, ⟨cell_bound_151, ⟨cell_bound_152, ⟨cell_bound_153, ⟨cell_bound_154, ⟨cell_bound_155, ⟨cell_bound_156, ⟨cell_bound_157, ⟨cell_bound_158, ⟨cell_bound_159, ⟨cell_bound_160, ⟨cell_bound_161, ⟨cell_bound_162, ⟨cell_bound_163, ⟨cell_bound_164, ⟨cell_bound_165, ⟨cell_bound_166, ⟨cell_bound_167, ⟨cell_bound_168, ⟨cell_bound_169, ⟨cell_bound_170, ⟨cell_bound_171, ⟨cell_bound_172, ⟨cell_bound_173, ⟨cell_bound_174, ⟨cell_bound_175, ⟨cell_bound_176, ⟨cell_bound_177, ⟨cell_bound_178, ⟨cell_bound_179, ⟨cell_bound_180, ⟨cell_bound_181, ⟨cell_bound_182, ⟨cell_bound_183, ⟨cell_bound_184, ⟨cell_bound_185, ⟨cell_bound_186, ⟨cell_bound_187, ⟨cell_bound_188, ⟨cell_bound_189, ⟨cell_bound_190, ⟨cell_bound_191, ⟨cell_bound_192, ⟨cell_bound_193, ⟨cell_bound_194, ⟨cell_bound_195, ⟨cell_bound_196, ⟨cell_bound_197, ⟨cell_bound_198, ⟨cell_bound_199, ⟨cell_bound_200, ⟨cell_bound_201, ⟨cell_bound_202, ⟨cell_bound_203, ⟨cell_bound_204, ⟨cell_bound_205, ⟨cell_bound_206, ⟨cell_bound_207, ⟨cell_bound_208, ⟨cell_bound_209, ⟨cell_bound_210, ⟨cell_bound_211, ⟨cell_bound_212, ⟨cell_bound_213, ⟨cell_bound_214, ⟨cell_bound_215, ⟨cell_bound_216, ⟨cell_bound_217, ⟨cell_bound_218, ⟨cell_bound_219, ⟨cell_bound_220, ⟨cell_bound_221, ⟨cell_bound_222, ⟨cell_bound_223, ⟨cell_bound_224, ⟨cell_bound_225, ⟨cell_bound_226, ⟨cell_bound_227, ⟨cell_bound_228, ⟨cell_bound_229, ⟨cell_bound_230, ⟨cell_bound_231, ⟨cell_bound_232, ⟨cell_bound_233, ⟨cell_bound_234, ⟨cell_bound_235, ⟨cell_bound_236, ⟨cell_bound_237, ⟨cell_bound_238, ⟨cell_bound_239, ⟨cell_bound_240, ⟨cell_bound_241, ⟨cell_bound_242, ⟨cell_bound_243, ⟨cell_bound_244, ⟨cell_bound_245, ⟨cell_bound_246, ⟨cell_bound_247, ⟨cell_bound_248, ⟨cell_bound_249, ⟨cell_bound_250, ⟨cell_bound_251, ⟨cell_bound_252, ⟨cell_bound_253, ⟨cell_bound_254, ⟨cell_bound_255, ⟨cell_bound_256, ⟨cell_bound_257, ⟨cell_bound_258, ⟨cell_bound_259, ⟨cell_bound_260, ⟨cell_bound_261, ⟨cell_bound_262, ⟨cell_bound_263, ⟨cell_bound_264, ⟨cell_bound_265, ⟨cell_bound_266, ⟨cell_bound_267, ⟨cell_bound_268, ⟨cell_bound_269, ⟨cell_bound_270, ⟨cell_bound_271, ⟨cell_bound_272, ⟨cell_bound_273, ⟨cell_bound_274, ⟨cell_bound_275, ⟨cell_bound_276, ⟨cell_bound_277, ⟨cell_bound_278, ⟨cell_bound_279, ⟨cell_bound_280, ⟨cell_bound_281, ⟨cell_bound_282, ⟨cell_bound_283, ⟨cell_bound_284, ⟨cell_bound_285, ⟨cell_bound_286, ⟨cell_bound_287, ⟨cell_bound_288, ⟨cell_bound_289, ⟨cell_bound_290, ⟨cell_bound_291, ⟨cell_bound_292, ⟨cell_bound_293, ⟨cell_bound_294, ⟨cell_bound_295, ⟨cell_bound_296, ⟨cell_bound_297, ⟨cell_bound_298, ⟨cell_bound_299, ⟨cell_bound_300, ⟨cell_bound_301, ⟨cell_bound_302, ⟨cell_bound_303, ⟨cell_bound_304, ⟨cell_bound_305, ⟨cell_bound_306, ⟨cell_bound_307, ⟨cell_bound_308, ⟨cell_bound_309, ⟨cell_bound_310, ⟨cell_bound_311, ⟨cell_bound_312, ⟨cell_bound_313, ⟨cell_bound_314, ⟨cell_bound_315, ⟨cell_bound_316, ⟨cell_bound_317, ⟨cell_bound_318, ⟨cell_bound_319, ⟨cell_bound_320, ⟨cell_bound_321, ⟨cell_bound_322, ⟨cell_bound_323, ⟨cell_bound_324, ⟨cell_bound_325, ⟨cell_bound_326, ⟨cell_bound_327, ⟨cell_bound_328, ⟨cell_bound_329, ⟨cell_bound_330, ⟨cell_bound_331, ⟨cell_bound_332, ⟨cell_bound_333, ⟨cell_bound_334, ⟨cell_bound_335, ⟨cell_bound_336, ⟨cell_bound_337, ⟨cell_bound_338, ⟨cell_bound_339, ⟨cell_bound_340, ⟨cell_bound_341, ⟨cell_bound_342, ⟨cell_bound_343, ⟨cell_bound_344, ⟨cell_bound_345, ⟨cell_bound_346, ⟨cell_bound_347, ⟨cell_bound_348, ⟨cell_bound_349, ⟨cell_bound_350, ⟨cell_bound_351, ⟨cell_bound_352, ⟨cell_bound_353, ⟨cell_bound_354, ⟨cell_bound_355, ⟨cell_bound_356, ⟨cell_bound_357, ⟨cell_bound_358, ⟨cell_bound_359, ⟨cell_bound_360, ⟨cell_bound_361, ⟨cell_bound_362, ⟨cell_bound_363, ⟨cell_bound_364, ⟨cell_bound_365, ⟨cell_bound_366, ⟨cell_bound_367, ⟨cell_bound_368, ⟨cell_bound_369, ⟨cell_bound_370, ⟨cell_bound_371, ⟨cell_bound_372, ⟨cell_bound_373, ⟨cell_bound_374, ⟨cell_bound_375, ⟨cell_bound_376, ⟨cell_bound_377, ⟨cell_bound_378, ⟨cell_bound_379, ⟨cell_bound_380, ⟨cell_bound_381, ⟨cell_bound_382, ⟨cell_bound_383, ⟨cell_bound_384, ⟨cell_bound_385, ⟨cell_bound_386, ⟨cell_bound_387, ⟨cell_bound_388, ⟨cell_bound_389, ⟨cell_bound_390, ⟨cell_bound_391, ⟨cell_bound_392, ⟨cell_bound_393, ⟨cell_bound_394, ⟨cell_bound_395, ⟨cell_bound_396, ⟨cell_bound_397, ⟨cell_bound_398, ⟨cell_bound_399, ⟨cell_bound_400, ⟨cell_bound_401, ⟨cell_bound_402, ⟨cell_bound_403, ⟨cell_bound_404, ⟨cell_bound_405, ⟨cell_bound_406, ⟨cell_bound_407, ⟨cell_bound_408, ⟨cell_bound_409, ⟨cell_bound_410, ⟨cell_bound_411, ⟨cell_bound_412, ⟨cell_bound_413, ⟨cell_bound_414, ⟨cell_bound_415, ⟨cell_bound_416, ⟨cell_bound_417, ⟨cell_bound_418, ⟨cell_bound_419, ⟨cell_bound_420, ⟨cell_bound_421, ⟨cell_bound_422, ⟨cell_bound_423, ⟨cell_bound_424, ⟨cell_bound_425, ⟨cell_bound_426, ⟨cell_bound_427, ⟨cell_bound_428, ⟨cell_bound_429, ⟨cell_bound_430, ⟨cell_bound_431, ⟨cell_bound_432, ⟨cell_bound_433, ⟨cell_bound_434, ⟨cell_bound_435, ⟨cell_bound_436, ⟨cell_bound_437, ⟨cell_bound_438, ⟨cell_bound_439, ⟨cell_bound_440, ⟨cell_bound_441, ⟨cell_bound_442, ⟨cell_bound_443, ⟨cell_bound_444, ⟨cell_bound_445, ⟨cell_bound_446, ⟨cell_bound_447, ⟨cell_bound_448, ⟨cell_bound_449, ⟨cell_bound_450, ⟨cell_bound_451, ⟨cell_bound_452, ⟨cell_bound_453, ⟨cell_bound_454, ⟨cell_bound_455, ⟨cell_bound_456, ⟨cell_bound_457, ⟨cell_bound_458, ⟨cell_bound_459, ⟨cell_bound_460, ⟨cell_bound_461, ⟨cell_bound_462, ⟨cell_bound_463, ⟨cell_bound_464, ⟨cell_bound_465, ⟨cell_bound_466, ⟨cell_bound_467, ⟨cell_bound_468, ⟨cell_bound_469, ⟨cell_bound_470, ⟨cell_bound_471, ⟨cell_bound_472, ⟨cell_bound_473, ⟨cell_bound_474, ⟨cell_bound_475, ⟨cell_bound_476, ⟨cell_bound_477, ⟨cell_bound_478, ⟨cell_bound_479, ⟨cell_bound_480, ⟨cell_bound_481, ⟨cell_bound_482, ⟨cell_bound_483, ⟨cell_bound_484, ⟨cell_bound_485, ⟨cell_bound_486, ⟨cell_bound_487, ⟨cell_bound_488, ⟨cell_bound_489, ⟨cell_bound_490, ⟨cell_bound_491, ⟨cell_bound_492, ⟨cell_bound_493, ⟨cell_bound_494, ⟨cell_bound_495, ⟨cell_bound_496, ⟨cell_bound_497, ⟨cell_bound_498, ⟨cell_bound_499, ⟨cell_bound_500, ⟨cell_bound_501, ⟨cell_bound_502, ⟨cell_bound_503, ⟨cell_bound_504, ⟨cell_bound_505, ⟨cell_bound_506, ⟨cell_bound_507, ⟨cell_bound_508, ⟨cell_bound_509, ⟨cell_bound_510, ⟨cell_bound_511, ⟨cell_bound_512, ⟨cell_bound_513, ⟨cell_bound_514, ⟨cell_bound_515, ⟨cell_bound_516, ⟨cell_bound_517, ⟨cell_bound_518, ⟨cell_bound_519, ⟨cell_bound_520, ⟨cell_bound_521, ⟨cell_bound_522, ⟨cell_bound_523, ⟨cell_bound_524, ⟨cell_bound_525, ⟨cell_bound_526, ⟨cell_bound_527, ⟨cell_bound_528, ⟨cell_bound_529, ⟨cell_bound_530, ⟨cell_bound_531, ⟨cell_bound_532, ⟨cell_bound_533, ⟨cell_bound_534, ⟨cell_bound_535, ⟨cell_bound_536, ⟨cell_bound_537, ⟨cell_bound_538, ⟨cell_bound_539, ⟨cell_bound_540, ⟨cell_bound_541, ⟨cell_bound_542, ⟨cell_bound_543, ⟨cell_bound_544, ⟨cell_bound_545, ⟨cell_bound_546, ⟨cell_bound_547, ⟨cell_bound_548, ⟨cell_bound_549, ⟨cell_bound_550, ⟨cell_bound_551, ⟨cell_bound_552, ⟨cell_bound_553, ⟨cell_bound_554, ⟨cell_bound_555, ⟨cell_bound_556, ⟨cell_bound_557, ⟨cell_bound_558, ⟨cell_bound_559, ⟨cell_bound_560, ⟨cell_bound_561, ⟨cell_bound_562, ⟨cell_bound_563, ⟨cell_bound_564, ⟨cell_bound_565, ⟨cell_bound_566, ⟨cell_bound_567, ⟨cell_bound_568, ⟨cell_bound_569, ⟨cell_bound_570, ⟨cell_bound_571, ⟨cell_bound_572, ⟨cell_bound_573, ⟨cell_bound_574, ⟨cell_bound_575, ⟨cell_bound_576, ⟨cell_bound_577, ⟨cell_bound_578, ⟨cell_bound_579, ⟨cell_bound_580, ⟨cell_bound_581, ⟨cell_bound_582, ⟨cell_bound_583, ⟨cell_bound_584, ⟨cell_bound_585, ⟨cell_bound_586, ⟨cell_bound_587, ⟨cell_bound_588, ⟨cell_bound_589, ⟨cell_bound_590, ⟨cell_bound_591, ⟨cell_bound_592, ⟨cell_bound_593, ⟨cell_bound_594, ⟨cell_bound_595, ⟨cell_bound_596, ⟨cell_bound_597, ⟨cell_bound_598, ⟨cell_bound_599, ⟨cell_bound_600, ⟨cell_bound_601, ⟨cell_bound_602, ⟨cell_bound_603, ⟨cell_bound_604, ⟨cell_bound_605, ⟨cell_bound_606, ⟨cell_bound_607, ⟨cell_bound_608, ⟨cell_bound_609, ⟨cell_bound_610, ⟨cell_bound_611, ⟨cell_bound_612, ⟨cell_bound_613, ⟨cell_bound_614, ⟨cell_bound_615, ⟨cell_bound_616, ⟨cell_bound_617, ⟨cell_bound_618, ⟨cell_bound_619, ⟨cell_bound_620, ⟨cell_bound_621, ⟨cell_bound_622, ⟨cell_bound_623, ⟨cell_bound_624, ⟨cell_bound_625, ⟨cell_bound_626, ⟨cell_bound_627, ⟨cell_bound_628, ⟨cell_bound_629, ⟨cell_bound_630, ⟨cell_bound_631, ⟨cell_bound_632, ⟨cell_bound_633, ⟨cell_bound_634, ⟨cell_bound_635, ⟨cell_bound_636, ⟨cell_bound_637, ⟨cell_bound_638, ⟨cell_bound_639, ⟨cell_bound_640, ⟨cell_bound_641, ⟨cell_bound_642, ⟨cell_bound_643, ⟨cell_bound_644, ⟨cell_bound_645, ⟨cell_bound_646, ⟨cell_bound_647, ⟨cell_bound_648, ⟨cell_bound_649, ⟨cell_bound_650, ⟨cell_bound_651, ⟨cell_bound_652, ⟨cell_bound_653, ⟨cell_bound_654, ⟨cell_bound_655, ⟨cell_bound_656, ⟨cell_bound_657, ⟨cell_bound_658, ⟨cell_bound_659, ⟨cell_bound_660, ⟨cell_bound_661, ⟨cell_bound_662, ⟨cell_bound_663, ⟨cell_bound_664, ⟨cell_bound_665, ⟨cell_bound_666, ⟨cell_bound_667, ⟨cell_bound_668, ⟨cell_bound_669, ⟨cell_bound_670, ⟨cell_bound_671, ⟨cell_bound_672, ⟨cell_bound_673, ⟨cell_bound_674, ⟨cell_bound_675, ⟨cell_bound_676, ⟨cell_bound_677, ⟨cell_bound_678, ⟨cell_bound_679, ⟨cell_bound_680, ⟨cell_bound_681, ⟨cell_bound_682, cell_bound_683⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem all_cell_bounds_relaxed : ∀ c ∈ cells,
    cellBound (c.1 : ℝ) (c.2 : ℝ) < -1329/200 := by
  intro c hc
  have h := all_cell_bounds c hc
  linarith

theorem interval_cell_certificate : ∀ t ∈ Set.Icc (0 : ℝ) 2,
    ∃ c ∈ cells, (c.1 : ℝ) ≤ t ∧ t ≤ c.2 ∧
      cellBound (c.1 : ℝ) (c.2 : ℝ) < -1329/200 := by
  intro t ht
  obtain ⟨c, hc, hlt, htr⟩ := cells_cover t ht
  exact ⟨c, hc, hlt, htr, all_cell_bounds_relaxed c hc⟩

#print axioms all_cell_bounds
#print axioms interval_cell_certificate
#print axioms energy_bounds
#print axioms cstar_bounds
#print axioms final_coefficient

end Zeta5AppendixNumerics
