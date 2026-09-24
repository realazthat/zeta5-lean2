import AppendixCellBase
import AppendixField.Batch027
import AppendixField.Batch028
import AppendixField.Batch029
import AppendixPotential.Batch028
import AppendixPotential.Batch029
import AppendixPotential.Batch030
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_224 : cellBound ((1324945925477/8000000000000 : ℚ) : ℝ) ((10656347439087/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1324945925477/8000000000000 : ℝ) ≤ (-208357281697739357537/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_224 (by norm_num)
  have hUr : potential (10656347439087/64000000000000 : ℝ) ≤ (-208357281697739357537/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_225 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_224
  linarith only [hU, hF]

theorem cell_bound_225 : cellBound ((10656347439087/64000000000000 : ℚ) : ℝ) ((5356563737179/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10656347439087/64000000000000 : ℝ) ≤ (-208038322667523964263/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_225 (by norm_num)
  have hUr : potential (5356563737179/32000000000000 : ℝ) ≤ (-208038322667523964263/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_226 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_225
  linarith only [hU, hF]

theorem cell_bound_226 : cellBound ((5356563737179/32000000000000 : ℚ) : ℝ) ((10769907509629/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5356563737179/32000000000000 : ℝ) ≤ (-20772344338030130367/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_226 (by norm_num)
  have hUr : potential (10769907509629/64000000000000 : ℝ) ≤ (-20772344338030130367/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_227 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_226
  linarith only [hU, hF]

theorem cell_bound_227 : cellBound ((10769907509629/64000000000000 : ℚ) : ℝ) ((108266875449/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10769907509629/64000000000000 : ℝ) ≤ (-41482495658261480989/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_227 (by norm_num)
  have hUr : potential (108266875449/640000000000 : ℝ) ≤ (-41482495658261480989/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_228 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_227
  linarith only [hU, hF]

theorem cell_bound_228 : cellBound ((108266875449/640000000000 : ℚ) : ℝ) ((10883467580171/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (108266875449/640000000000 : ℝ) ≤ (-103552637640551291091/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_228 (by norm_num)
  have hUr : potential (10883467580171/64000000000000 : ℝ) ≤ (-103552637640551291091/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_229 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_228
  linarith only [hU, hF]

theorem cell_bound_229 : cellBound ((10883467580171/64000000000000 : ℚ) : ℝ) ((5470123807721/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10883467580171/64000000000000 : ℝ) ≤ (-103400846843336689257/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_229 (by norm_num)
  have hUr : potential (5470123807721/32000000000000 : ℝ) ≤ (-103400846843336689257/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_230 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_229
  linarith only [hU, hF]

theorem cell_bound_230 : cellBound ((5470123807721/32000000000000 : ℚ) : ℝ) ((10997027650713/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5470123807721/32000000000000 : ℝ) ≤ (-206501603306400501383/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_230 (by norm_num)
  have hUr : potential (10997027650713/64000000000000 : ℝ) ≤ (-206501603306400501383/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_231 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_230
  linarith only [hU, hF]

theorem cell_bound_231 : cellBound ((10997027650713/64000000000000 : ℚ) : ℝ) ((345431490187/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10997027650713/64000000000000 : ℝ) ≤ (-6443902587136349597/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_231 (by norm_num)
  have hUr : potential (345431490187/2000000000000 : ℝ) ≤ (-6443902587136349597/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_232 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_231
  linarith only [hU, hF]

theorem cell_bound_232 : cellBound ((345431490187/2000000000000 : ℚ) : ℝ) ((5583683878263/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (345431490187/2000000000000 : ℝ) ≤ (-200801862509345983/97656250000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_232 (by norm_num)
  have hUr : potential (5583683878263/32000000000000 : ℝ) ≤ (-200801862509345983/97656250000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_233 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_232
  linarith only [hU, hF]

theorem cell_bound_233 : cellBound ((5583683878263/32000000000000 : ℚ) : ℝ) ((2820231956767/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5583683878263/32000000000000 : ℝ) ≤ (-410099095097263021/200000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_233 (by norm_num)
  have hUr : potential (2820231956767/16000000000000 : ℝ) ≤ (-410099095097263021/200000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_234 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_233
  linarith only [hU, hF]

theorem cell_bound_234 : cellBound ((2820231956767/16000000000000 : ℚ) : ℝ) ((1139448789761/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2820231956767/16000000000000 : ℝ) ≤ (-102244740955708248953/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_234 (by norm_num)
  have hUr : potential (1139448789761/6400000000000 : ℝ) ≤ (-102244740955708248953/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_235 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_234
  linarith only [hU, hF]

theorem cell_bound_235 : cellBound ((1139448789761/6400000000000 : ℚ) : ℝ) ((1438505996019/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1139448789761/6400000000000 : ℝ) ≤ (-203940268741140348801/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_235 (by norm_num)
  have hUr : potential (1438505996019/8000000000000 : ℝ) ≤ (-203940268741140348801/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_236 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_235
  linarith only [hU, hF]

theorem cell_bound_236 : cellBound ((1438505996019/8000000000000 : ℚ) : ℝ) ((2933792027309/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1438505996019/8000000000000 : ℝ) ≤ (-101436080373340239973/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_236 (by norm_num)
  have hUr : potential (2933792027309/16000000000000 : ℝ) ≤ (-101436080373340239973/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_237 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_236
  linarith only [hU, hF]

theorem cell_bound_237 : cellBound ((2933792027309/16000000000000 : ℚ) : ℝ) ((149528603129/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2933792027309/16000000000000 : ℝ) ≤ (-40368253335372189699/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_237 (by norm_num)
  have hUr : potential (149528603129/800000000000 : ℝ) ≤ (-40368253335372189699/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_238 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_237
  linarith only [hU, hF]

theorem cell_bound_238 : cellBound ((149528603129/800000000000 : ℚ) : ℝ) ((3047352097851/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (149528603129/800000000000 : ℝ) ≤ (-50211077399611563333/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_238 (by norm_num)
  have hUr : potential (3047352097851/16000000000000 : ℝ) ≤ (-50211077399611563333/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_239 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_238
  linarith only [hU, hF]

theorem cell_bound_239 : cellBound ((3047352097851/16000000000000 : ℚ) : ℝ) ((1552066066561/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3047352097851/16000000000000 : ℝ) ≤ (-99939262948279612413/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_239 (by norm_num)
  have hUr : potential (1552066066561/8000000000000 : ℝ) ≤ (-99939262948279612413/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_240 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_239
  linarith only [hU, hF]

#print axioms cell_bound_239
end Zeta5AppendixNumerics
