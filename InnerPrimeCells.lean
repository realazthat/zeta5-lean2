import InnerPrimeCells.Batch000
import InnerPrimeCells.Batch001
import InnerPrimeCells.Batch002
import InnerPrimeCells.Batch003
import InnerPrimeCells.Batch004
import InnerPrimeCells.Batch005
import InnerPrimeCells.Batch006
import InnerPrimeCells.Batch007
import InnerPrimeCells.Batch008
import InnerPrimeCells.Batch009
import InnerPrimeCells.Batch010
import InnerPrimeCells.Batch011
import InnerPrimeCells.Batch012
import InnerPrimeCells.Batch013
import InnerPrimeCells.Batch014
import InnerPrimeCells.Batch015

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace Zeta5InnerAsymptotics

def innerCellLeft : Fin 143 → ℚ := ![3,(70/23),(120/37),(140/43),(10/3),(80/23),(7/2),(160/43),(140/37),(90/23),4,(180/43),(160/37),(100/23),(9/2),(200/43),(110/23),(180/37),5,(220/43),(120/23),(200/37),(11/2),(240/43),(130/23),(220/37),6,(260/43),(140/23),(240/37),(13/2),(280/43),(150/23),(20/3),(160/23),(300/43),7,(260/37),(170/23),(320/43),(15/2),(280/37),(180/23),(340/43),8,(300/37),(190/23),(360/43),(17/2),(320/37),(200/23),(380/43),9,(210/23),(340/37),(400/43),(19/2),(220/23),(360/37),(420/43),10,(440/43),(380/37),(240/23),(21/2),(460/43),(400/37),(250/23),11,(480/43),(260/23),(420/37),(23/2),(500/43),(270/23),(440/37),12,(520/43),(280/23),(460/37),(25/2),(540/43),(290/23),(480/37),13,(560/43),(300/23),(40/3),(310/23),(580/43),(27/2),(500/37),(320/23),(600/43),14,(520/37),(330/23),(620/43),(29/2),(540/37),(340/23),(640/43),15,(560/37),(350/23),(660/43),(31/2),(360/23),(580/37),(680/43),16,(370/23),(600/37),(700/43),(33/2),(380/23),(50/3),(720/43),(620/37),(390/23),17,(740/43),(640/37),(400/23),(35/2),(760/43),(410/23),(660/37),18,(780/43),(420/23),(680/37),(37/2),(800/43),(430/23),(700/37),19,(820/43),(440/23),(720/37),(39/2),(840/43),(450/23)]

def innerCellRight : Fin 143 → ℚ := ![(70/23),(120/37),(140/43),(10/3),(80/23),(7/2),(160/43),(140/37),(90/23),4,(180/43),(160/37),(100/23),(9/2),(200/43),(110/23),(180/37),5,(220/43),(120/23),(200/37),(11/2),(240/43),(130/23),(220/37),6,(260/43),(140/23),(240/37),(13/2),(280/43),(150/23),(20/3),(160/23),(300/43),7,(260/37),(170/23),(320/43),(15/2),(280/37),(180/23),(340/43),8,(300/37),(190/23),(360/43),(17/2),(320/37),(200/23),(380/43),9,(210/23),(340/37),(400/43),(19/2),(220/23),(360/37),(420/43),10,(440/43),(380/37),(240/23),(21/2),(460/43),(400/37),(250/23),11,(480/43),(260/23),(420/37),(23/2),(500/43),(270/23),(440/37),12,(520/43),(280/23),(460/37),(25/2),(540/43),(290/23),(480/37),13,(560/43),(300/23),(40/3),(310/23),(580/43),(27/2),(500/37),(320/23),(600/43),14,(520/37),(330/23),(620/43),(29/2),(540/37),(340/23),(640/43),15,(560/37),(350/23),(660/43),(31/2),(360/23),(580/37),(680/43),16,(370/23),(600/37),(700/43),(33/2),(380/23),(50/3),(720/43),(620/37),(390/23),17,(740/43),(640/37),(400/23),(35/2),(760/43),(410/23),(660/37),18,(780/43),(420/23),(680/37),(37/2),(800/43),(430/23),(700/37),19,(820/43),(440/23),(720/37),(39/2),(840/43),(450/23),20]

def innerCellSlope : Fin 143 → ℚ := ![(18/5),(49/20),(283/40),(283/40),(277/40),(231/40),(271/40),(71/20),(27/5),(17/4),(17/5),(17/5),(321/40),(55/8),(63/8),(93/20),(7/2),(107/20),(9/2),(9/2),(67/20),(319/40),(359/40),(23/4),(23/5),(129/20),(28/5),(28/5),(89/20),(363/40),(403/40),(137/20),(57/10),(69/10),(23/4),(23/4),(49/10),(27/4),(28/5),(19/8),(27/8),8,(137/20),(137/20),6,(157/20),(67/10),(139/40),(179/40),(91/10),(159/20),(159/20),(71/10),(119/20),(39/5),(183/40),(223/40),(177/40),(181/20),(181/20),(69/10),(147/40),(221/40),(35/8),(43/8),(43/8),10,(177/20),8,(191/40),(29/8),(219/40),(259/40),(259/40),(213/40),(199/20),(91/10),(47/8),(189/40),(263/40),(303/40),(303/40),(257/40),(221/20),(51/5),(279/40),(233/40),(145/8),(679/40),(679/40),(719/40),(793/40),(747/40),(309/20),(73/5),(769/40),(723/40),(723/40),(763/40),(837/40),(791/40),(331/20),(157/10),(813/40),(767/40),(767/40),(807/40),(761/40),(167/8),(353/20),(84/5),(313/20),(811/40),(811/40),(851/40),(161/8),(799/40),(67/4),(93/5),(349/20),(83/5),(83/5),(849/40),(803/40),(843/40),(357/20),(167/10),(371/20),(177/10),(177/10),(331/20),(847/40),(887/40),(379/20),(89/5),(393/20),(94/5),(94/5),(353/20),(891/40),(931/40),(401/20),(189/10)]

def innerCellConstant : Fin 143 → ℚ := ![-6,(-5/2),(-35/2),(-35/2),-17,-13,(-33/2),(-9/2),(-23/2),-7,-11,-11,-31,-26,(-61/2),(-31/2),-10,-19,-24,-24,-18,-43,(-97/2),(-61/2),-24,-35,-41,-41,-34,-64,(-141/2),(-99/2),-42,-50,-42,-42,-49,-62,(-107/2),(-59/2),-37,-72,-63,-63,-71,-86,(-153/2),(-99/2),-58,-98,-88,-88,-97,(-173/2),(-207/2),(-147/2),-83,-72,-117,-117,-114,-81,-100,-88,(-197/2),(-197/2),(-297/2),-136,-147,-111,-98,-119,(-261/2),(-261/2),-117,-172,-184,-145,-131,-154,(-333/2),(-333/2),-152,-212,-225,-183,-168,-184,(-337/2),(-337/2),-182,-207,-191,-146,-160,-225,(-417/2),(-417/2),-223,-250,-233,-185,-200,-270,(-505/2),(-505/2),-268,-250,-279,-228,-244,(-451/2),(-601/2),(-601/2),-317,-298,(-591/2),(-483/2),(-545/2),-253,-270,-270,-350,-330,(-695/2),(-581/2),-270,-303,-321,-321,-300,-385,(-807/2),(-687/2),-322,-357,-376,-376,-354,-444,(-927/2),(-801/2),-378]

theorem innerKernel_on_cells (i : Fin 143) (x : ℚ)
    (hl : innerCellLeft i≤x) (hr : x < innerCellRight i) :
    innerKernel x=innerCellSlope i*x+innerCellConstant i := by
  fin_cases i
  · exact innerKernel_cell_000 x hl hr
  · exact innerKernel_cell_001 x hl hr
  · exact innerKernel_cell_002 x hl hr
  · exact innerKernel_cell_003 x hl hr
  · exact innerKernel_cell_004 x hl hr
  · exact innerKernel_cell_005 x hl hr
  · exact innerKernel_cell_006 x hl hr
  · exact innerKernel_cell_007 x hl hr
  · exact innerKernel_cell_008 x hl hr
  · exact innerKernel_cell_009 x hl hr
  · exact innerKernel_cell_010 x hl hr
  · exact innerKernel_cell_011 x hl hr
  · exact innerKernel_cell_012 x hl hr
  · exact innerKernel_cell_013 x hl hr
  · exact innerKernel_cell_014 x hl hr
  · exact innerKernel_cell_015 x hl hr
  · exact innerKernel_cell_016 x hl hr
  · exact innerKernel_cell_017 x hl hr
  · exact innerKernel_cell_018 x hl hr
  · exact innerKernel_cell_019 x hl hr
  · exact innerKernel_cell_020 x hl hr
  · exact innerKernel_cell_021 x hl hr
  · exact innerKernel_cell_022 x hl hr
  · exact innerKernel_cell_023 x hl hr
  · exact innerKernel_cell_024 x hl hr
  · exact innerKernel_cell_025 x hl hr
  · exact innerKernel_cell_026 x hl hr
  · exact innerKernel_cell_027 x hl hr
  · exact innerKernel_cell_028 x hl hr
  · exact innerKernel_cell_029 x hl hr
  · exact innerKernel_cell_030 x hl hr
  · exact innerKernel_cell_031 x hl hr
  · exact innerKernel_cell_032 x hl hr
  · exact innerKernel_cell_033 x hl hr
  · exact innerKernel_cell_034 x hl hr
  · exact innerKernel_cell_035 x hl hr
  · exact innerKernel_cell_036 x hl hr
  · exact innerKernel_cell_037 x hl hr
  · exact innerKernel_cell_038 x hl hr
  · exact innerKernel_cell_039 x hl hr
  · exact innerKernel_cell_040 x hl hr
  · exact innerKernel_cell_041 x hl hr
  · exact innerKernel_cell_042 x hl hr
  · exact innerKernel_cell_043 x hl hr
  · exact innerKernel_cell_044 x hl hr
  · exact innerKernel_cell_045 x hl hr
  · exact innerKernel_cell_046 x hl hr
  · exact innerKernel_cell_047 x hl hr
  · exact innerKernel_cell_048 x hl hr
  · exact innerKernel_cell_049 x hl hr
  · exact innerKernel_cell_050 x hl hr
  · exact innerKernel_cell_051 x hl hr
  · exact innerKernel_cell_052 x hl hr
  · exact innerKernel_cell_053 x hl hr
  · exact innerKernel_cell_054 x hl hr
  · exact innerKernel_cell_055 x hl hr
  · exact innerKernel_cell_056 x hl hr
  · exact innerKernel_cell_057 x hl hr
  · exact innerKernel_cell_058 x hl hr
  · exact innerKernel_cell_059 x hl hr
  · exact innerKernel_cell_060 x hl hr
  · exact innerKernel_cell_061 x hl hr
  · exact innerKernel_cell_062 x hl hr
  · exact innerKernel_cell_063 x hl hr
  · exact innerKernel_cell_064 x hl hr
  · exact innerKernel_cell_065 x hl hr
  · exact innerKernel_cell_066 x hl hr
  · exact innerKernel_cell_067 x hl hr
  · exact innerKernel_cell_068 x hl hr
  · exact innerKernel_cell_069 x hl hr
  · exact innerKernel_cell_070 x hl hr
  · exact innerKernel_cell_071 x hl hr
  · exact innerKernel_cell_072 x hl hr
  · exact innerKernel_cell_073 x hl hr
  · exact innerKernel_cell_074 x hl hr
  · exact innerKernel_cell_075 x hl hr
  · exact innerKernel_cell_076 x hl hr
  · exact innerKernel_cell_077 x hl hr
  · exact innerKernel_cell_078 x hl hr
  · exact innerKernel_cell_079 x hl hr
  · exact innerKernel_cell_080 x hl hr
  · exact innerKernel_cell_081 x hl hr
  · exact innerKernel_cell_082 x hl hr
  · exact innerKernel_cell_083 x hl hr
  · exact innerKernel_cell_084 x hl hr
  · exact innerKernel_cell_085 x hl hr
  · exact innerKernel_cell_086 x hl hr
  · exact innerKernel_cell_087 x hl hr
  · exact innerKernel_cell_088 x hl hr
  · exact innerKernel_cell_089 x hl hr
  · exact innerKernel_cell_090 x hl hr
  · exact innerKernel_cell_091 x hl hr
  · exact innerKernel_cell_092 x hl hr
  · exact innerKernel_cell_093 x hl hr
  · exact innerKernel_cell_094 x hl hr
  · exact innerKernel_cell_095 x hl hr
  · exact innerKernel_cell_096 x hl hr
  · exact innerKernel_cell_097 x hl hr
  · exact innerKernel_cell_098 x hl hr
  · exact innerKernel_cell_099 x hl hr
  · exact innerKernel_cell_100 x hl hr
  · exact innerKernel_cell_101 x hl hr
  · exact innerKernel_cell_102 x hl hr
  · exact innerKernel_cell_103 x hl hr
  · exact innerKernel_cell_104 x hl hr
  · exact innerKernel_cell_105 x hl hr
  · exact innerKernel_cell_106 x hl hr
  · exact innerKernel_cell_107 x hl hr
  · exact innerKernel_cell_108 x hl hr
  · exact innerKernel_cell_109 x hl hr
  · exact innerKernel_cell_110 x hl hr
  · exact innerKernel_cell_111 x hl hr
  · exact innerKernel_cell_112 x hl hr
  · exact innerKernel_cell_113 x hl hr
  · exact innerKernel_cell_114 x hl hr
  · exact innerKernel_cell_115 x hl hr
  · exact innerKernel_cell_116 x hl hr
  · exact innerKernel_cell_117 x hl hr
  · exact innerKernel_cell_118 x hl hr
  · exact innerKernel_cell_119 x hl hr
  · exact innerKernel_cell_120 x hl hr
  · exact innerKernel_cell_121 x hl hr
  · exact innerKernel_cell_122 x hl hr
  · exact innerKernel_cell_123 x hl hr
  · exact innerKernel_cell_124 x hl hr
  · exact innerKernel_cell_125 x hl hr
  · exact innerKernel_cell_126 x hl hr
  · exact innerKernel_cell_127 x hl hr
  · exact innerKernel_cell_128 x hl hr
  · exact innerKernel_cell_129 x hl hr
  · exact innerKernel_cell_130 x hl hr
  · exact innerKernel_cell_131 x hl hr
  · exact innerKernel_cell_132 x hl hr
  · exact innerKernel_cell_133 x hl hr
  · exact innerKernel_cell_134 x hl hr
  · exact innerKernel_cell_135 x hl hr
  · exact innerKernel_cell_136 x hl hr
  · exact innerKernel_cell_137 x hl hr
  · exact innerKernel_cell_138 x hl hr
  · exact innerKernel_cell_139 x hl hr
  · exact innerKernel_cell_140 x hl hr
  · exact innerKernel_cell_141 x hl hr
  · exact innerKernel_cell_142 x hl hr

def innerIntegral : ℚ := ∑ i : Fin 143,
  (innerCellSlope i*(1/innerCellLeft i-1/innerCellRight i)+
    innerCellConstant i/2*(1/(innerCellLeft i)^2-1/(innerCellRight i)^2))

theorem innerIntegral_exact : innerIntegral = (322437603634266857629/7535670527041937280000) := by
  norm_num [innerIntegral,innerCellSlope,innerCellConstant,innerCellLeft,innerCellRight,Fin.sum_univ_succ]

#print axioms innerKernel_on_cells
#print axioms innerIntegral_exact
end Zeta5InnerAsymptotics
