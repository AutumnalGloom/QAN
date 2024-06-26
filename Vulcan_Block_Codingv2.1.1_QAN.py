#==============================================================================
# Program to calculate parameters for blasthole data in Grade Control
#==============================================================================

# Mar 2, 2018: Created from BlastCalc MineSight access version - MEI
# Apr 2, 2018: Added waste categories to Orct4 - KJP
# Apr 11, 2018 - v1.7.2: added check for Weathered and Oxide when searching for applicable GEOL code;
# July 29, 2018 - v1.7.3: revised calculation of Blasting Agent reactivity flag (BRXNF) and renamed REACT item SHCRR to prevent confusion with blasting reactivity;
# Jan 1, 2019 - v1.7.6: added third c/o for LG-PR to HG;added MG ore code which is split into 10MG-N and 11MG-PR;
#                       removed GEOL codes 9, 17, 19, 30, 31, and 34 as no longer used and created 2D arrays by deposit; simplified MET for Aqqaluk to Regular and Weathered;
#                       revised ORCT2 with removal of code 7 (all weathered in 2), filtering of high RPB into Weathered, and creation of 2D arrays by deposit; modified ORCT4 to follow ORCT2;
# Feb 24, 2019: Changed Orct2 to identify normal, bariritic and high FE in wethered ore and to code ore as weathered when RPb is greater than 40% in Exhalite.
# Mar 02, 2019: Changed Orct4 Zn binning now 0-15% Zn_LG, 15-25% Zn_MG and >25% Zn_HG (previously 0 to 10%, 10 to 20%, >20%) for grade control
# Mar 30, 2019: SPBlimit added to line 92
# Apr 23, 2019 - v1.8.0: updated costs for LOM 2020; changed sPb and T1/T2/T6 defaults to QAN2016 model; added GEOL1 for Qanaiyaq weathered geology search and altered ORCT2 logic as a consequence; set GEOL groups to new Qan codes;
#                        modified geology search in block models to use GEOSM instead of GEOL; added WXFG code (ORCT2 == 2 or ORCT2 == 7); revised MET for Aqqaluk to Regular and Weathered;
#                        removed CoverType GEOL group as KeyCreek flag made it redundant; revised blasting reagent-rock reactivity coding from rework of 2014 and 2016 data;
#                        modified WARDC=2 to accept: i) all Construction rock, GEOL 3, 4 (A) & 200 (Q) as they have no grades, and ii) grade criteria acceptable Exhalite and Baritic rock;
# Dec 12, 2019: Changed lead concentrate to match Minesight blasthole script.  Previously Pb recovery was being set 0 if RPb>=40%
# Jan 7, 2021 - v1.9.2: removed pre-VIP2 option coding; set P80 to 65um; added efficency for TPH and Zn Recovery (all concentrates); removed "Construction" geology group; changed Cover criteria to include Zn and total sulfides;
#                        redefined highTPH upper limit to 5.5Mt/yr (672 tpoh) and set limit for Oxide Pb-Ag and Weathered Zn-Cu; changed selling cost to new (flat rate) contract terms;
#                        simplified coding for WXFG, QWXFG, and BRXNF; changed QWXFG setting based on RPB and workSTSPB limits to MET=2 (thus Weathered Met not exactly same criteria between Aqq and Qan);
#                        redefined OpCost calculation logic and naming to be consistent with DEST script; set to maximize Weathered feed over Sulfide feed when more valuable; add extra flotation cost for Oxide Pb-Ag;
#                        updated costs for 2021-5YR based on 'EcM LOM 2021 - 20200719.xlsx' R&R parameters; cutoffs & logic set for LG-PR implementation per 2021 Budget;
# Feb 11, 2022 - v1.9.3   Updated the costs for LOM 2022; the block model that is being used are (RED2018_E.bmf and QAN2016_F.bmf), the operating cutoff is updated with the LOM 2022 (3.60 $/s)
# Nov 20, 2022 - v1.9.4 [CMM] Removed ORCT2 = 7 as a condition for SP_OX oxide "ore" & used MinGrade (3.0%) as upper limit for Ba% permitted in WARDC = 3 (W_CV cover) classification;
#                       Script was misclassifying material as oxide and misclassifying barren Siksikpuk barite as cover in areas where resource model GEOL indicated Kivalina or Kayak.
# Dec 10, 2022 - v2.0.0 [CMM] Update with 2023 economics from QAN2016_G & RED2018_F.  
#                       Zn price, SiPenalty, PbPayZn, BkPayAg, ZnFreight, PbFreight, portsite, dewatering, NWABTeff costs updated (see AMR 5.23.1.py). Note SRK recommended PbPayZn changes but no notes/memo on why or how this was determined.
#                       Mine, mill, tails, indirect, averageTPH, haulIncrLU & haulIncroLD updated (see DEST 11.52.2.py)
#                       TPG_eff reduced to 1.09 (see ModelCalcs 24.52.5.py)
#                       ZNGRD for mill feed dropped from 55.0% to 53.0% and PBGRD increased from 54.0% to 54.5%.  (see ModelCalcs 24.52.5.py)
#                       Strat Planning changed Paalaaq/Aqq MET 7 or 8 ZNGRD and PBGRD values but BW confirmed should not change so leaving ZNGRD & PBGRD for Paalaaq MET 7 or 8. 
# Dec 18, 2023 - v2.1.0 [CMM] Update with 2024 economics from QAN2016_I & RED2018_H (note that QAN2016_H & RED2018_G were used for 2024 LOM but QAN2016_I & RED2018_H are from 5YBP and used for 2024 budget)
#                       Zn price, ZnTcBase, ZnTcBasis, GePayment, PbTcBase, PbPayZn, ZnFreight, PbFreight, portsite, dewatering, NWABTeff costs updated (see AMR 5.23.3.py)
#                       Mine, mill, tails, rehandle, indirect, averageTPH, postCost, comminutionCost, haulIncrLU, haulIncroLD, default DPScutoff updated (see DEST 11.52.5.py)
#                       Version number changed but current version is reverted to match 2023, therefore no change from 2023. (see ModelCalcs 24.52.7.py)
# Feb 26, 2024 - v2.1.1 [AR; AJ] Update GEO codes for QAN22v6; will work with either LTM GEO codes (backwards compatible).  Oxide coding is now in GEOL1; not GEOSM

from collections import Counter
from math import pow, pi, exp, log, sin
import sys
import vulcan
from shapely.geometry import Point
from shapely.geometry.polygon import Polygon

#==============================================================================
# Constants
#==============================================================================

# Models
Vulcan_refModel = ["RED2018_H.bmf","QAN2016_I.bmf"]

# Zn or Pb minimum grade for testing if GEOL code questionable; Ba minimum grade check for Cover (W_CV)
MinGrade = 3.0

# Rock density parameters
# Qanaiyaq
Solids_Q, TFbase_Q = 0.98123, 13.4512 # %, ft3/st
PBt_Q, ZNt_Q, FEt_Q, BAt_Q = 0.106020557, 0.084082061, 0.148471822, 0.107594420 # pre-calculated
# calculation basis: PBt_Q, ZNt_Q, FEt_Q, BAt_Q = (TFbase_Q-4.27)/86.5983, (TFbase_Q-7.81)/67.0916, (TFbase_Q-6.54)/46.5489, (TFbase_Q-7.12)/58.8428
Qan_Black_Shale_TF, Qan_Siksikpuk_Shale_TF = 14.5013, 12.5812 # ft3/st. NOTE: Siksikpuk TF based on a 20%/80% blend of Baritic Siksikpuk and Siksikpuk as both interpreted together in QAN2016 model.
## Qan_Black_Shale_TF, Qan_Siksikpuk_Shale_TF, Qan_Baritic_Siksikpuk_Shale_TF = 14.5013, 13.2210, 10.0216 # ft3/st {saved should Baritic Siksikpuk be interpreted separately from Siksikpuk again in future}

# Aqqaluk, Main
Solids_A, TFbase_A = 0.96194, 11.7934 # %, ft3/st
PBt_A, ZNt_A, FEt_A, BAt_A = 0.086877156, 0.059372768, 0.112857963, 0.079422020 # pre-calculated
# calculation basis: PBt_A, ZNt_A, FEt_A, BAt_A = (TFbase_A-4.27)/86.5983, (TFbase_A-7.81)/67.0916, (TFbase_A-6.54)/46.5489, (TFbase_A-7.12)/58.8428
Black_Shale_TF, Siksikpuk_Shale_TF, Baritic_Siksikpuk_Shale_TF = 12.1796, 11.6755, 7.9942 # ft3/st

# Paalaaq
Solids_P, TFbase_P = 0.99938, 12.4978 # %, ft3/st
PBt_P, ZNt_P, FEt_P, BAt_P = 0.095010891,0.069871364,0.127989741,0.091392348 # pre-calculated
# calculation basis: PBt_P, ZNt_P, FEt_P, BAt_P = (TFbase_P-4.27)/86.5983, (TFbase_P-7.81)/67.0916, (TFbase_P-6.54)/46.5489, (TFbase_P-7.12)/58.8428

# Deposit specific grade and grain size calculation defauts
AGcoeffZN = [0.028529, 0.028529, 0.028529, 0.020184]  # AG assay regression, based on DEP code [Main(=Aqqaluk), Aqqaluk, Paalaaq(=Aqqaluk), Qaniayaq]
AGcoeffPB = [0.360182, 0.360182, 0.360182, 0.460805]  # "
AGinter =   [0.164318, 0.164318, 0.164318, 0.335686]  # "
pctRPBnonweathered = [0.19, 0.19, 0.19, 0.32] # %, mean/median of all non-Weathered in pit > breakeven c/o, based on DEP code [Main(=Aqqaluk), Aqqaluk, Paalaaq(=Aqqaluk), Qaniayaq]
pctRPBweathered = [0.61, 0.61, 0.61, 0.51]    # %, mean/median of all Weathered in pit > breakeven c/o, based on DEP code [Main(=Aqqaluk), Aqqaluk, Paalaaq(=Aqqaluk), Qaniayaq]
S = [0.035, 0.035, 0.035, 0.545] # "
TOC50 = [0.32, 0.32, 0.32, 0.51] # "
CU50 = 0.0095  # %, mean/median default (GEOL=22), only required for Qanaiyaq

# Texture defaults for Sulfide host rock (array is [M,A,P,Q])
T1_baritic = [31,29,69,52]
T2_baritic = [11,1,10,3]
T6_baritic = [58,70,21,45]
T1_vein = [32,29,32,0] # no "Vein" type in Qanaiyaq
T2_vein = [32,45,40,0]
T6_vein = [36,26,28,0]
T1_exhalite = [48,40,51,50]
T2_exhalite = [17,15,18,15]
T6_exhalite = [35,45,31,35]
T1_weathered = [48,40,51,50] # Qanaiyaq is only deposit with specific "Weathered" default, other deposits use same as exhalite
T2_weathered = [17,15,18,10]
T6_weathered = [35,45,31,40]

# Block model minimum grades for calculations
NSGmin, ZNmin, PBmin, BAmin, FEmin, FEinZN  = 0.5, 0.1, 0.1, 0.1, 1.0, 0.035/0.6709 # % FEinZN assumes 3.5% Fe in Sphalerite

# Grade based ORCT2 assignment limitS
BAlimit, FElimit, RPBlimit, SPBlimit = 7.0, 8.0, 40.0, 2.0 # %

# MET assignment limits
BAlimitWeathered, RPBlimitPB = 4.9, 45.0 # %
RPBlimitOX, SPBlimitOX, ZNPBmaxOX = 46.5, 8.5, 0.585 # %
CUlimitLO, CUlimitHI = 0.18, 0.32 # 0.15% Cu minimal effect and 0.25% Cu strong effect, limits are 0.25 +/-0.07
CUlimitSlp, CUlimitInt = 1/(CUlimitHI-CUlimitLO), 1+CUlimitLO/(CUlimitHI-CUlimitLO)

# GEOL code group for plates, ORCT1
Block_1_Q = [11,21,31,41,51,61] # QAN [Exhalite High Grade, Exhalite Low Grade, High-Pb Weathered, Exhalite High Iron, Exhalite High Barium,Exhalite Low Barium]
Block_2_Q = [12,22,32,42,52,62] # QAN [ExhaliteExhalite High Grade, Exhalite Low Grade, High-Pb Weathered, Exhalite High Iron, Exhalite High Barium,Exhalite Low Barium]
Block_3_Q = [13,23,33,43,53,63] # QAN [Exhalite High Grade, Exhalite Low Grade, High-Pb Weathered,Exhalite High Barium]
Block_4_Q = [14,24,34,44,54,64] # QAN added for the new model
Block_5_Q = [16,26,36,46,56,66] # QAN added for the new model , all undefined will make ORCT1=6
Middle_Plate_A = [1, 6, 11, 15]
Lower_Plate_A = [2, 8, 12, 13, 14, 16, 18]
Sublower_Plate_P = [7, 10, 20, 21]

# GEOL codes for metallurgy, ORCT, rock segregation, and recovery formulas (2D array is [M,A,P,Q])
Air = 0
bariteGEOLlimit, zincGEOLlimit, OXzincGEOLlimit, OXleadGEOLlimit = 20, 15, 3, 10 # % for default GEOL setting
Exhalite = [[1, 8, 11, 18], [1, 8, 11, 18], [20, 21], [10,11,12,13,14,16,20,21,22,23,24,26,40,41,42,43,44,46,60,61,62,63,64,66]] # ORCT2, Aqqaluk and Paalaaq MET, and WARDC, QAN LIST includes Vein unit 110 and 120
Vein = [[6, 13, 14], [6, 13, 14], [10], [110,120]]                     # ORCT2 and Aqqaluk and Paalaaq MET
Baritic = [[15, 16], [15, 16], [7], [50,51,52,53,54,56]]        # ORCT2, Aqqaluk and Paalaaq MET, and WARDC #QAN List [Exhalite High Barium (51,52,53)]
Baritic_Siksikpuk = [[3], [3], [3], []]                         # ORCT2, WARDC, and for setting default values in waste blocks
Siksikpuk = [[4], [4], [4], [200,207]]                              # ORCT2, WARDC, and for setting default values in waste blocks # QAN List [Siksikpuk 200]
Black_Shale = [[25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [201, 202, 203]] # QAN List, Black shale comprises of [Ikalukrok, Kivalina,Basal Melange (201,202,203)]
Weathered = [[2, 12], [2, 12], [], [80,81, 82, 83,84,86,100, 101, 102, 103,104,106]] # ORCT2 and Aqqaluk MET {QAN codes are in GEOL1} # QAN List [Weathered Exhalite (81,82,83), High Weathered Copper (101,102,103)]
Oxide = [[], [], [], [30,31,32,33,34,36]]                       # ORCT2 and Qanaiyaq MET # QAN List [High Pb Weathered (30s coded in GEOL1)]
BA_shale_reactive = [[26], [26], [26], [201]]                   # BRXNF exception for Ikalukrok shale # QAN List [Ikalukrok (201)]
SulfideHost = [Exhalite[0]+Weathered[0]+Oxide[0]+Vein[0]+Baritic[0], Exhalite[1]+Weathered[1]+Oxide[1]+Vein[1]+Baritic[1], Exhalite[2]+Weathered[2]+Oxide[2]+Vein[2]+Baritic[2], Exhalite[3]+Weathered[3]+Oxide[3]+Vein[3]+Baritic[3]]

# Destination codes for materials are:
HG    = 1  # High Grade (Direct Mill Feed)
LG_N  = 2  # Low Grade Non-reactive
LG_PR = 3  # Low Grade Possibly Reactive
W_PR  = 4  # Waste Possibly Reactive
W_N   = 5  # Waste Non-reactive
W_CN  = 6  # Waste Construction
W_CV  = 7  # Waste Cover
SP_OX = 8  # Oxide (High Pb/Ag)
SP_WX = 9  # Weathered (High Cu/Zn)
MG_N  = 10 # Middle Grade Non-reactive - NO LONGER USED (as of 2020)
MG_PR = 11 # Middle Grade Possibly Reactive - NO LONGER USED (as of 2020)

# kernel matrix (initialization) for 3x3x3 area
# middle slab
#  5  6  7
#  3  -  4
#  0  1  2
# lower slab
# 14 15 16
# 11 12 13
#  8  9 10
# upper slab
# 23 24 25
# 20 21 22
# 17 18 19
MTX = [0]*26; MTXg1 = [0]*26

# Concentrate Recovery Calculation Limit
ZNadjPBmin, PBadjPBmin = 0.1, 0.1 #

# Concentrate recovery limits
recLimitFE, recLimitZN, recLimitBA = 7, 7, 23 # %
ZnRecMin, ZnRecMax = 30, 93 # %
PbRecMin, PbRecMax = 15, 84 # %
AgRecZnMax, AgRecPbMax,  = 71, 87 # %
PbRecPbOxMax, AgRecPbOxMax = 87, 77 # %

# PCA class boundaries
PCA1 = Polygon([(0.07739765,-0.065052144,1),(0,-0.44449356,1),(0.7596754,-1.9022361,1),(1.8326122,-1.3898741,1),(0.77248174,-0.5780578,1),(0.07739765,-0.065052144,1)])
PCA2 = Polygon([(-0.32426587,-2.3706815,1),(0.7596754,-1.9022361,1),(0,-0.44449356,1),(-0.17570537,-1.3971936,1),(-0.32426587,-2.3706815,1)])
PCA3 = Polygon([(1.3209039,0.57174075,1),(3.224679,-0.44566396,1),(1.8326122,-1.3898741,1),(0.77248174,-0.5780578,1),(1.3209039,0.57174075,1)])
PCA4 = Polygon([(-0.73650986,-1.245879,1),(-0.17570537,-1.3971936,1),(-0.32426587,-2.3706815,1),(-0.6433958,-2.5317097,1),(-0.9405167,-2.3194454,1),(-1.1420099,-2.0472643,1),(-0.73650986,-1.245879,1)])
PCA5 = Polygon([(-0.17570537,-1.3971936,1),(0,-0.44449356,1),(-0.43072304,-0.31878603,1),(-0.6500919,-1.0023206,1),(-0.73650986,-1.245879,1),(-0.17570537,-1.3971936,1)])
PCA6 = Polygon([(0,-0.44449356,1),(0.07739765,-0.065052144,1),(0.33600292,1.0987418,1),(0,1.2890476,1),(-0.29675466,1.2451309,1),(-0.87999207,0.1545316,1),(-0.5769689,-0.16165164,1),(-0.43072304,-0.31878603,1),(0,-0.44449356,1)])
PCA7 = Polygon([(-0.87999207,0.1545316,1),(-1.7136983,-1.1987387,1),(-1.4677393,-1.5680045,1),(-0.5769689,-0.16165164,1),(-0.87999207,0.1545316,1)])
PCA8 = Polygon([(-1.4677393,-1.5680045,1),(-1.1420099,-2.0472643,1),(-0.73650986,-1.245879,1),(-0.6500919,-1.0023206,1),(-0.43072304,-0.31878603,1),(-0.5769689,-0.16165164,1),(-1.4677393,-1.5680045,1)])
PCA9 = Polygon([(1.3209039,0.57174075,1),(0.33600292,1.0987418,1),(0.07739765,-0.065052144,1),(0.77248174,-0.5780578,1),(1.3209039,0.57174075,1)])
PCA10 = Polygon([(-0.29675466,1.2451309,1),(-1.6172923,0.9157553,1),(-1.7136983,-1.1987387,1),(-0.87999207,0.1545316,1),(-0.29675466,1.2451309,1)])
PCA11 = Polygon([(-1.1420099,-2.0472643,1),(-1.474234,-2.619543,1),(-0.946019,-3.6442673,1),(-0.4783286,-3.702823,1),(-0.32426587,-2.3706815,1),(-0.6433958,-2.5317097,1),(-0.9405167,-2.3194454,1),(-1.1420099,-2.0472643,1)])

# === Grinding model parameters (T. Kojovic 2016 spreadsheet model) ===
# 1) Hardness estimate limits
Ab_min, Ab_max = 15.0, 300.0# TK o riginal model limits
BBMWi_max = 24.0 # kWh/mt, TK original model limits based on Main/Aqq were min=3 & max=30, replaced lower limit with equation based on Ab

# 2) Mill power calculation (same for SAG or Ball)
# general parameters
Kmill = 1.26
SGliquid = 1.0
SGball = 7.8
Cgvty = 9.825 # m/s2, acceleration to gravity (at 68 degrees latitude...)
halfPI = pi/2
# SAG motor installed power: 1&2 = 1500 kW, Sag3 = 2000 kW; 93% mech & elec eff => max load power 1400 kW and 1850 kW
sag_radius, sag_belly, sag_center, sag_trunion = 6.48/2, 2.19, 3.51, 1.59 # metres

# 3) Pebble crusher parameters
# Pebble Crusher installed power is 200 kW, max load power is 186 kW (200 kW x 93% eff), and no-load power is 15 kW
TPH_pebble_expected, pebble_port, pebble_CCS, pebble_fx, pebble_K2 = 50.0, 65.0, 13.0, 0.295, 1.19 # tph, mm, mm, m, K = 1.00 for all crushers operating in closed circuit with a classifying screen, 1.19 if the crusher is in open circuit, e.g. pebble crusher in a AG/SAG circuit
pebble_F80, pebble_P80 = 0.65*pebble_port*1000, 0.65*pebble_CCS*1000 # microns
F80_fx = -(pebble_fx + pebble_F80/1000000) # metre
P80_fx = -(pebble_fx + pebble_P80/1000000) # metre
PRpcr_const = pebble_K2*4*pow(pebble_P80,P80_fx) - pow(pebble_F80,F80_fx)

# 4) Throughput calculation
CSS = 100.0 # mm, Pri estimate
CSSconst = pow(CSS,0.7)
screen_aper = 15.8 # mm
PRbm  = 4118.0 # kW, Ball Mill max load power (between 4115 & 4120)
PRim_nl = 150.0 # kW, IsaMill no-load power
Kbm = [0.617000, 0.699717, 0.592349] # BM Specific Energy parameter K [Std, Pebble-crush, Pre-crush]
Ksag, n1, n2, n3 = [0.620773, 0.583098, 0.547004], 0.2907477955, 0.7072333907, -0.5 # SAG Specific Energy parameters for: Constant[Std, Pebble-crush, Pre-crush], DWIAB, BBMWi, P80(actually T80...)
C1, C2, C3, C4 = 1.88202, -0.0323806, -0.413931, 0.0106230 # DWIAB parameters
k1, k2, k3, k4, k5, k6, k7, k8, k9 = [-1391.42, -1451.01, -1268.13], 1.96831, 24.8088, 6.82504*100, 81.8772*100, -3.29940*10000, -0.813952, -2.79288, 9.51851 # T80 parameters for: Constant[Std, Pebble-crush, Pre-crush], Ab, BBMWi, CS, ML, ML*BC, F80, %-1", screen_aper (k4,k5,k6 adjusted for non-%, i.e. x100, x100, x10000)
F80min, F80max, P1max = 15, 165, 90.0 # mm, mm, %; TK suggestions 15mm, 200mm, & 90%; lowered F80max to: (100mm+38mm throw)*120%
highTPH = 672.0   # mt/hr, for SAG/BM limit flag and Oxide and Weathered limiting, 672tph (5.5 Mt/yr) is "high" as throughput with BBMWi of 3 kWh/mt is about 827 tph for non-VIP2 case

# 5) user input values for Throughput model
gc = 0 # Grinding Configuration: 0-Standard, 1-Pebble crusher, 2-Pre-crush
Solids_W_fr = 0.75 # fraction of solids by weight (default = 0.75)
# post-VIP2 SAG mill parameters (*** parameters are expected to be the same, but until post-VIP2 operated through 2020 and actual seen the SAG1_2 and SAG3 option has been left in the coding ***)
RPMsag1_2 = 225 # SAG Mill RPM
RPMsag3 = 225
BCsag1_2 = 0.140 # SAG Ball Charge "ball filling", fraction
BCsag3 = 0.140
MLsag1_2 = 0.254 # SAG Mill Load "total filling", fraction
MLsag3 = 0.254
# calculate SAG Critical Speed (fractional) from RPM
CSsag_const = pow(2*sag_radius,0.5)/(42.3*18.16) # fraction of critical speed calculation Konstant for equations below
CSsag1_2, CSsag3 = RPMsag1_2*CSsag_const, RPMsag3*CSsag_const
# === end Grinding model parameters ===

# Throughput and recovery efficency
TPH_eff, ZnRec_eff = 1.09, 1.022 # Race 23 "better" case, "PTV500" +9% and +2.2% total increase (note: not incremental) This is now the Base Case for LOM 2023, updated Jan 19, 2022

# NSR/AMR calculation parameters
ZnPrice, PbPrice, AgPrice = 1.20, 0.90, 20.00 # $/lb, $/lb, $/tr oz

##   ZnTcBase, ZnTcBasisN3, ZnTcBasisN2, ZnTcBasisN1, ZnTcBasis, ZnTcBasisP1, ZnTcBasisP2, ZnTcBasisP3, ZnTcBasisP4 = 251.20, 1500.0, 2000.0, 2100.0, 2300.0, 2500.0, 3000.0, 3500.0, 3750.0  # $/t
##   ZnBelowBasisN3, ZnBelowBasisN2, ZnBelowBasisN1, ZnBelowBasis, ZnAboveBasis, ZnAboveBasisP1, ZnAboveBasisP2, ZnAboveBasisP3, ZnAboveBasisP4  = -0.0165, -0.0343, -0.0619, -0.0623, 0.0705, 0.0617, 0.0469, 0.0365, 0.0304 # $/$
ZnTcBase, ZnTcBasis = 260.0, 0.0  # $/t
ZnBelowBasis, ZnAboveBasis  = 0.0, 0.0  # $/$
GePayment = (0.08-0.065)*0.20*((1000.0/0.69405)-120) # $/t, equation is: (grade - deduct)* pay *(( [GeO2 price] /[GeO2 conversion]) - refine)
SiPenalty = (0.0400-0.0325)*1.50  # $/t based on 5 year average SiO2
ZnFlatPenalty = 0.00 # $/t
ZnPayZn, ZnDeductZn = 0.85, 0.08 # %, %
ZnPayAg, ZnDeductAg, ZnRefineAg = 0.70, 3.000*31.10348, 0.0 # %, g/t, $/g
ZnPayPb = 0.0 # %

PbTcBase, PbTcBasis = 150.0, 2000.0 # $/t, $/t
PbBelowBasis, PbAboveBasis = 0.0, 0.0 # $/$, $/$
PbFlatPenalty = 0.00 # $/t
PbPayPb, PbDeductPb = 0.95, 0.03 # %, %
PbPayAg, PbDeductAg, PbRefineAg = 0.95, 42.210, 0.782/31.10348 # %, g/t, $/g
PbPayZn = 0.098 # %  0.1*50%*50% from SRK consultants Q1 2022 change from 0.0998%: "Pay is only 50%, since the other 50% smelter does not pay for the the Zn in Pb Conc"

BkPayAg, BkDeductAg = 0.70, 3.000*31.10348 # %, g/t

ZnCGreduction = 0.0075 # %
PbCGreduction = 0.0 # %
# do not use any oxidation reduction with Bulk conc as unknown

# shipping costs
ZnFreight = 101.47 # $/dmt
PbFreight = 103.63 # $/dmt
BkFreight = (ZnFreight + PbFreight)/2 # $/dmt

# other concentrate costs
portsite = 23.71  # $/t concentrate (ops, road maintenance, catering)
dewatering = 10.11 # $/t concentrate (labor, maintenance, & power)
BII = 0.0031 # business interruption insurance, against gross (vs. payable) concentrate revenue
NWABTeff = 0.0271 # NW Arctic Borough Tax: schedule weighted average of i) 4.50% Severance Tax and ii) depreciation based PILT+VIF charge. This is against gross concentrate revenue less treatment and freight charges (sell expense not deducted).

#selling expense
ZnSell, PbSell = 2.79, 2.97 # $/dmt concentrate
BkSell = (ZnSell + PbSell)/2 # $/dmt concentrate

# mining and milling cost (array is [M,A,P,Q])
mine_waste_cost = [5.96, 5.96, 5.96, 5.43] # $/t waste rock
mine_ore_cost = [5.88, 5.88, 5.88, 5.61]   # $/t ore rock
mill_cost = [28.48, 28.48, 28.48, 26.55]   # $/t mill feed
mill_oxide = 25.92                         # $/t Oxide Pb-Ag mill feed - NOTE that Vulcan GC oxide is based on classificiation via blasthole assays only so costs for mill_oxide irrelevant for Grade Control purposes
tailsCostPerTonne = 7.94                   # $/t tailings, includes dam construction
rehandle_cost = 0.206                      # $/t mill feed, incremental rehandle cost for extra tram distance from LGO (or OXID) stockpile to crusher
indirect_cost = 23711.53                   # $/hr grinding, based on total LOM G&A cost divided by total LOM mill grinding hours (could also be annual G&A cost divided by Available Mill Operating Hours per year, i.e. 365 x 24 x 93.5%)

# cost escalators for grinding energy and throughput (array is [M,A,P,Q])
averagePower = 18.7 # kwh/t (SAG mill + Ball mill specific energy)
powerCost = 0.223 # $/kwh ($60/barrel long term)
comminutionCost = [10.02, 10.02, 10.02, 8.49] # $/t, crushing and grinding (no labor)
averageTPH = [500, 500, 500, 590]  # tph, plan average  from last similar LOM schedule (2023 onwards LOM 5-YR, Taken from MP tab for AQQ and QAN)

# cost escalator for elevation (array is [M,A,P,Q])
haulIncrLU = 0.0159 # $/t/bench for benches above index ("Loaded Up"), +0.303min/bench, excludes horizontal distance
haulIncrLD = 0.0184 # $/t/bench for benches below index ("Loaded Down"), +0.351min/bench, includes horizontal distance
haulIncrElev = [925, 925, 925, 1300] # bench index (17, 17, 17, 12)

# operating cutoffs
DPScutoff = 1.00 # $/s, this is primary (or LG-N) cutoff iterated when maximizing NPV
DPScutoffMG = 20.00 # $/s, this is secondary (or LG-PR) cutoff when maximizing NPV in LG-PR milling options, Ensure that this particular cutoff is greater than the DPScutoff to exclude the MG
DPScutoffLG = 0.00 # $/s, this is tertiary (or LG-PR to HG) cutoff when maximizing NPV in partial LG-PR milling options

# Qanaiyaq Weathered value realization
maximizeWX = True   # if False then maximize Sulfide Mill feed; if True then maximize Weathered Mill feed, i.e. if a Bulk Concentrate gives a higher cash flow than Zinc & Lead Concentrates then make a Bulk Concentrate

#==============================================================================
# Constants which are calculated
#==============================================================================

# IsaMill parameters based on VIP2
P80fine, P80medium, P80coarse = 65.0, 65.0, 65.0 # um
PRim = 2081.0 # kW, maximum, not net, power from IsaMill (nominally 835 kW in TK2016, however maximum is 3000 hp x 0.746 kW/hp x 93% motor eff = 2081 kW)
PFimVbm = 23.895*pow(PRim-PRim_nl,-0.377) # Power Factor, IsaMill vs Ball Mill
PRim_net = (PRim-PRim_nl)*PFimVbm*1.0753  # net IsaMill power (in Ball Mill power equivalent)

# base treatment and selling costs
ZnPricet = ZnPrice*2204.62
PbPricet = PbPrice*2204.62
AgPriceg = AgPrice/31.10348
ZnConcPayPb = PbPricet*ZnPayPb
PbConcPayZn = ZnPricet*PbPayZn

# zinc treatment charge calc
if ZnPricet > ZnTcBasis:
   ZnTc = ZnTcBase + (ZnPricet-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
else:
   ZnTc = ZnTcBase + (ZnTcBasis-ZnPricet)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty

# lead treatment charge calc
if PbPricet > PbTcBasis:
   PbTc = PbTcBase + (PbPricet-PbTcBasis)*PbAboveBasis + PbFlatPenalty
else:
   PbTc = PbTcBase + (PbTcBasis-PbPricet)*PbBelowBasis + PbFlatPenalty

# bulk concentrate treatment charge calc
# zinc treatment charge calc
if ZnPricet > ZnTcBasis:
   ZnTcBk = ZnTcBase + (ZnPricet-ZnTcBasis)*ZnAboveBasis
else:
   ZnTcBk = ZnTcBase + (ZnTcBasis-ZnPricet)*ZnBelowBasis
# lead treatment charge calc
if PbPricet > PbTcBasis:
   PbTcBk = PbTcBase + (PbPricet-PbTcBasis)*PbAboveBasis
else:
   PbTcBk = PbTcBase + (PbTcBasis-PbPricet)*PbBelowBasis
BkTc = (ZnTcBk + PbTcBk)/2

#==============================================================================
# Execution Function
#==============================================================================

modelPath = sys.argv[1]   # modelPath = r"E:\repos\_scripting\Vulcan_GC2\Aqq_bh_5.bmf"
# modelPath=  r"E:\repos\_scripting\Vulcan_GC2\Aqq_bh_5.bmf"

with vulcan.block_model(modelPath, "w") as bm:
   bm.rewind()
   pitname = bm.get_string("area").upper()

if pitname == 'AQQ':
   MDL = 0
   isQanaiyaq = False
elif pitname == 'QAN':
   MDL = 1
   isQanaiyaq = True
else:
   print("Invalid Mining Area")
   sys.exit()

# Reference block model names, based on model [RED20xx, QAN20xx]
refModel = Vulcan_refModel[MDL]  # refModel = r"E:\repos\_scripting\Vulcan_GC2\Aqq_red15_2020.bmf"

print("Starting execution...")

with vulcan.block_model(modelPath, "w") as bm, vulcan.block_model(refModel, "r") as refm:
   for block in bm:
      # get ZN
      workZN = block["zn"]
      if workZN < 0: # if <0 then exit to next block
         continue

      # determine block coordinate in refm model
      (xworld, yworld, zworld) = (block["xworld"], block["yworld"], block["zworld"])
      refm.find_world_xyz(xworld, yworld, zworld)
      # get location items
      DEP = int(refm.get("DEP"))  # ensure an integer
      d = DEP - 1
      isPaalaaq = (DEP == 3)
      workELEV = block["zworld"] - 12.5
      workVOL = block["volume"]

      # get remaining grade items
      workPB = block["pb"]
      workFE = block["fe"]
      workBA = block["ba"]
      workSPB = block["spb"] ##### sPb froom core and RC holes, PB: Pb from core and RC hole
      # no need to determine SPB, done in the blasthole script
      # check that PB >= SPB and, if lower, set to SPB value
      if workSPB > workPB:
         workPB = workSPB
         replace_PB = True
      else:
         replace_PB = False
      workSIO2 = block["sio2"]
      workAG = block["ag"]
      if workAG < 0 or workAG > 80:  # then unlikely to be an assay so estimate silver from regression
         workAG = AGcoeffZN[d] * workZN + AGcoeffPB[d] * workPB + AGinter[d]
      AGM = 34.2857*workAG
      if isQanaiyaq: #### Q pit coding starts here:
         workCU = block["cu"]
      workTOC = block["toc"]
      if workTOC < 0: # if not in blasthole model try in reference model
         workTOC = refm.get("TOC")
         if workTOC < 0: # if not in reference model use median value
            workTOC = TOC50[d]
      workS = refm.get("S")
      if workS < 0: # if not in model use median value
         workS = S[d]
      # get Key Creek boolean
      if DEP == 2: # Aqqaluk, so get flag from model
         KeyCreek = refm.get("KCFLG") #### KCFLG: Flag for block in Key Creek Plate
      else: # Main, Paalaaq, Qanaiyaq, so not present
         KeyCreek = False

      # calculate RPB ratio  *** this section could be simplified, a side-effect of blasthole assay script conversion ***
      if workPB > 0 and workSPB >= 0:
         RPB_defined = True
         workRPB = int(round(workSPB / workPB * 100.0))
      else:
         RPB_defined = False
         workRPB = 0
      # determine RPB from blasthole assays (called RPBb)
      if workSPB < 0: ##### soluble Pb
         RPBb = -1
      elif workPB > 0: ##### Pb grade
         RPBb = int(round(workSPB / workPB * 100.0))
      else:
         RPBb = 0
      RPBm = refm.get("rpb") ##### ratio stsPb/stPb
      # determine RPB for GEOL estimation (if required when suitable GEOL code not found)
      if RPBb > -1: # blasthole assay based value exists
         geolRPB = RPBb
      elif RPBm > -1: # Block Model value exists
         geolRPB = RPBm
      else: # no means to estimate
         geolRPB = 0

      # calculate ZNPB ratio
      if workPB > 0:
         ZNPB = round(workZN/workPB,2)
         ZNPB_defined = True
      else:
         ZNPB = 0
         ZNPB_defined = False

      # calculate Fe in Sphalerite lattice, thus FeS rather than ZnS
      if workZN > 0:
         FEinFeS = workZN*min(workFE/workZN,FEinZN)
         FEinFeS2 = workFE - FEinFeS
      else:
         FEinFeS = 0.0
         FEinFeS2 = workFE

      # NSG or Mineral Sum calculations for BA
      if workSIO2 < 0: # SiO2 not assayed, so calculate NSG to use in BA adjustment
         NSG = 100.0 - (workZN/0.6709 + (workPB-workSPB)/0.8660 + workSPB/0.6832 + FEinFeS2/0.4655 + FEinFeS/0.6352 + workBA/0.5884 + workS + workTOC)
         if NSG < NSGmin: # adjust calculated NSG and Ba to put into Block Model if require change due to mineral sum total
            deltaNSG = NSGmin - NSG
            BAcalc =  round((workBA/0.5884 - deltaNSG)*0.5884,2)
            if BAcalc < BAmin:
               workBA = min(workBA,BAmin)
            else:
               workBA = BAcalc
   #SiO2 check is done in blasthole script, need to check.
      else:  # SiO2 assayed, so just check mineral sum for BA adjustment
         mineralSum = workSIO2 + workZN/0.6709 + (workPB-workSPB)/0.8660 + workSPB/0.6832 + FEinFeS2/0.4655 + FEinFeS/0.6352 + workBA/0.5884 + workS + workTOC
         if mineralSum > 100:
            BAcalc = round((100.0 - (workSIO2 + workZN/0.6709 + (workPB-workSPB)/0.8660 + workSPB/0.6832 + FEinFeS2/0.4655 + FEinFeS/0.6352 + workS + workTOC))*0.5884,2)
            if BAcalc < BAmin:
               workBA = min(workBA,BAmin)
            else:
               workBA = BAcalc
      NSG = max(100.0 - (workZN/0.6709 + (workPB-workSPB)/0.8660 + workSPB/0.6832 + FEinFeS2/0.4655 + FEinFeS/0.6352 + workBA/0.5884 + workS + workTOC),0.0)

      # reset geology code if required
      workGEOL = block["geol"]
      workGEOSM = refm.get("geosm") # GEOSM - sulfide mineral preference majority geology code, so mixed shale/sulfide blocks get sulfide code, unmixed blocks have simple majority code (GEOL)
      workGEOL1 = block["geol1"] # GEOL1 - secondary geology description in Qanaiyaq, generally for weathering
      hasMinGrade = (workZN > MinGrade or workPB > MinGrade)
      if hasMinGrade: # grade is above minimum threshold so test if GEOL code is a Sulphide host and, if so, whether a Weathered or Oxide sulphide
         # test if Sulphide, if Weathered, and if Oxide
         FailSulphideTest = not(workGEOSM in SulfideHost[d])
         isWeathered = geolRPB > RPBlimit
         if isQanaiyaq:
            FailWeatheredTest = not(workGEOL1 in Weathered[d]) and isWeathered
            isOxide = geolRPB >= RPBlimitOX and workSPB >= SPBlimitOX and ZNPB_defined and ZNPB < ZNPBmaxOX
            FailOxideTest = (not(workGEOSM in Oxide[d]) or not(workGEOL1 in Oxide[d])) and isOxide          #need to test AR 2-26-24
            if workGEOSM in Oxide[d] and isOxide:
               workGEOL = workGEOSM
            elif workGEOL1 in Oxide[d] and isOxide: #Oxide coding in QAN22 model with GEOL1
               workGEOL = workGEOL1
            elif workGEOL1 in Weathered[d] and isWeathered:
               workGEOL = workGEOL1
            elif workGEOSM in SulfideHost[d]:
               workGEOL = workGEOSM
         else: # Aqqaluk, Main, Paalaaq
            FailWeatheredTest = not(workGEOSM in Weathered[d]) and isWeathered
            isOxide = False
            FailOxideTest = False
            if (workGEOSM in Weathered[d] and isWeathered) or workGEOSM in SulfideHost[d]:
              workGEOL = workGEOSM
      else:
         FailSulphideTest = False
         FailWeatheredTest = False
         FailOxideTest = False
         workGEOL = workGEOSM # set to block if below minimum LG grades
#
#See Blasthole_Coding_v1.8.0.py line 590 onwards for matrix
#
      ORCT1 = refm.get("ORCT1")
      geolChange = (FailSulphideTest or FailWeatheredTest or FailOxideTest)  # True if GEOL will be from an adjacent model block or default
      if geolChange:
         block_size = refm.model_schema_size(0)
         search_ext = (xworld - block_size[0],
                       xworld + block_size[0],
                       yworld - block_size[1],
                       yworld + block_size[1],
                       zworld - block_size[2],
                       zworld + block_size[2])
         search_str = '-X -bw %.2f %.2f %.2f %.2f %.2f %.2f' % (search_ext[0],search_ext[1],search_ext[2],search_ext[3],search_ext[4],search_ext[5])
         sel_ext = refm.get_matches(search_str)
         MTX = refm.get_data("GEOL", sel_ext)
         if isQanaiyaq and isWeathered:  # need Weathered search exception for Qanaiyaq as weathering is in GEOL1 code
            modeMTXg1 = Counter(MTXg1).most_common(4) # pick top 4 sorts as only go 4 deep in code below, i.e. from a practical standpoint if you have to pick the 5th most common code is this really a worthwhile estimate anymore...
            workGEOL1 = modeMTXg1[0][0]  # first mode, count starts at 0; example: MTXg1 is [1,3,4,6,6,6,5,5] => modeMTXg1 is [(6, 3), (5, 2), (1, 1), (3, 1), (4, 1)]
            blockCount_g1 = modeMTXg1[0][1]
            FailWeatheredTest = not(workGEOL1 in Weathered[d]) and isWeathered
            if blockCount_g1 < 26 and FailWeatheredTest: # get second mode
               workGEOL1 = modeMTXg1[1][0]
               blockCount_g1 = blockCount_g1 + modeMTXg1[1][1]
               FailWeatheredTest = not(workGEOL1 in Weathered[d]) and isWeathered
               if blockCount_g1 < 26 and FailWeatheredTest: # get third mode
                  workGEOL1 = modeMTXg1[2][0]
                  blockCount_g1 = blockCount_g1 + modeMTXg1[2][1]
                  FailWeatheredTest = not(workGEOL1 in Weathered[d]) and isWeathered
                  if blockCount_g1 < 26 and FailWeatheredTest: # get fourth mode
                     workGEOL1 = modeMTXg1[3][0]
                     FailWeatheredTest = not(workGEOL1 in Weathered[d]) and isWeathered
         else: # general Sulphide check for Aqqaluk or Qanaiyaq, and specific Aqqaluk/isWeathered or Qanaiyaq/isOxide checks
            modeMTX = Counter(MTX).most_common(4) # pick top 4 sorts as only go 4 deep in code below, i.e. from a practical standpoint if you have to pick the 5th most common code is this really a worthwhile estimate anymore...
            workGEOSM = modeMTX[0][0]  # first mode, count starts at 0; example: MTX is [1,3,4,6,6,6,5,5] => modeMTX is [(6, 3), (5, 2), (1, 1), (3, 1), (4, 1)]
            blockCount = modeMTX[0][1]
            FailSulphideTest = not(workGEOSM in SulfideHost[d])
            if isQanaiyaq:
               FailOxideTest = not(workGEOSM in Oxide[d]) and isOxide
            else:
               FailWeatheredTest = not(workGEOSM in Weathered[d]) and isWeathered
            if blockCount < 26 and (FailSulphideTest or FailWeatheredTest or FailOxideTest) and len(modeMTX) >= 2: # get second mode
               workGEOSM = modeMTX[1][0]
               blockCount = blockCount + modeMTX[1][1]
               FailSulphideTest = not(workGEOSM in SulfideHost[d])
               if isQanaiyaq:
                  FailOxideTest = not(workGEOSM in Oxide[d]) and isOxide
               else:
                  FailWeatheredTest = not(workGEOSM in Weathered[d]) and isWeathered
               if blockCount < 26 and (FailSulphideTest or FailWeatheredTest or FailOxideTest) and len(modeMTX) >= 3: # get third mode
                  workGEOSM = modeMTX[2][0]
                  blockCount = blockCount + modeMTX[2][1]
                  FailSulphideTest = not(workGEOSM in SulfideHost[d])
                  if isQanaiyaq:
                     FailOxideTest = not(workGEOSM in Oxide[d]) and isOxide
                  else:
                     FailWeatheredTest = not(workGEOSM in Weathered[d]) and isWeathered
                  if blockCount < 26 and (FailSulphideTest or FailWeatheredTest or FailOxideTest) and len(modeMTX) >= 4: # get fourth mode
                     workGEOSM = modeMTX[3][0]
                     FailSulphideTest = not(workGEOSM in SulfideHost[d])
                     if isQanaiyaq:
                        FailOxideTest = not(workGEOSM in Oxide[d]) and isOxide
                     else:
                        FailWeatheredTest = not(workGEOSM in Weathered[d]) and isWeathered

         if FailSulphideTest or FailWeatheredTest or FailOxideTest: # if suitable GEOL code not found in 3x3 matrix then set a default sulfide host geology
            if MDL == 0: # not Qanaiyaq (Note: Veined units 6, 10, 13, 14, and 17 require physical observation to tag so not auto-settable)
               if workBA >= bariteGEOLlimit: # baritic default
                  if ORCT1 == 8: # Lower plate
                     workGEOL = 16 ##### this is just a geology code
                  elif ORCT1 == 1: # Middle plate
                     workGEOL = 15 ##### Geology code
                  else: # Sub-Lower plate
                     workGEOL = 7 #####
               else:
                  if workZN >= zincGEOLlimit: # higher grade exhalite default
                     if geolRPB > RPBlimit: # weathered, no plate distinction
                        workGEOL = 12
                     else: # non-weathered
                        if ORCT1 == 8: # Lower plate
                           workGEOL = 18
                        elif ORCT1 == 1: # Middle plate
                           workGEOL = 11
                        else: # Sub-Lower plateMDL
                           workGEOL = 18 # should be 20
                  else: # lower grade exhalite default
                     if geolRPB > RPBlimit: # weathered, no plate distinction
                        workGEOL = 2
                     else: # non-weathered
                        if ORCT1 == 8: # Lower plate
                           workGEOL = 8
                        elif ORCT1 == 1: # Middle plate
                           workGEOL = 1
                        else: # Sub-Lower plate
                           workGEOL = 8 #should be 21
            else: # MDL == 1, Qanaiyaq
               if ORCT1 <= 1: # 1_Block
                  if workZN >= zincGEOLlimit:
                     if geolRPB > RPBlimit:
                        workGEOL = 81 # weathered exhalite default (GEOL1 setting)
                     else:
                        workGEOL = 11 # higher grade exhalite default (GEOL setting)
                  else: # workZN < zincGEOLlimit
                     if workZN < OXzincGEOLlimit and workPB >= OXleadGEOLlimit:
                        workGEOL = 31 # very low grade oxide default (GEOL setting)
                     else:
                        if geolRPB > RPBlimit:
                           workGEOL = 81 # weathered exhalite default (GEOL1 setting)
                        else:
                           workGEOL = 21 # lower grade exhalite default (GEOL setting)
               elif ORCT1 <= 2: # 2_Block
                  if workZN >= zincGEOLlimit:
                     if geolRPB > RPBlimit:
                        workGEOL = 82 # weathered exhalite default (GEOL1 setting)
                     else:
                        workGEOL = 12 # higher grade exhalite default (GEOL setting)
                  else: # workZN < zincGEOLlimit
                     if workZN < OXzincGEOLlimit and workPB >= OXleadGEOLlimit:
                       workGEOL = 32 # very low grade oxide default (GEOL setting)
                     else:
                        if geolRPB > RPBlimit:
                           workGEOL = 82 # weathered exhalite default (GEOL1 setting)
                        else:
                           workGEOL = 22 # lower grade exhalite default (GEOL setting)
               else: # 3_Block, and default  #test AR 2-26-24 will now catch all defaults ending in 3; not zero
                  if workZN >= zincGEOLlimit:
                    if geolRPB > RPBlimit:
                        workGEOL = 83 # weathered exhalite default (GEOL1 setting)
                    else:
                        workGEOL = 13 # higher grade exhalite default (GEOL setting)
                  else: # workZN < zincGEOLlimit
                     if workZN < OXzincGEOLlimit and workPB >= OXleadGEOLlimit:
                        workGEOL = 33 # very low grade oxide default (GEOL setting)
                     else:
                        if geolRPB > RPBlimit:
                           workGEOL = 83 # weathered exhalite default (GEOL1 setting)
                        else:
                           workGEOL = 23 # lower grade exhalite default (GEOL setting)
         else: # suitable geology code found in 3x3x3 matrix search
            if isQanaiyaq:
               if not FailOxideTest and isOxide:
                  workGEOL = workGEOSM  #test AR 2-26-24
               elif not FailWeatheredTest and isWeathered:
                  workGEOL = workGEOL1
               else:
                  workGEOL = workGEOSM
            else:
               workGEOL = workGEOSM

      # get texture, but need to know workGEOL for defaults, so use workGEOL at this point
      workT1 = refm.get("t1")
      workT2 = refm.get("t2")
      workT6 = refm.get("t6")
      if (workT1 + workT2 + workT6) <= 98: # if not ~100(%), use median value defaults
         if workGEOL in Baritic[d]:
            workT1 = T1_baritic[d]
            workT2 = T2_baritic[d]
            workT6 = T6_baritic[d]
         elif workGEOL in Vein[d]:
              workT1 = T1_vein[d]
              workT2 = T2_vein[d]
              workT6 = T6_vein[d]
         elif workGEOL in Weathered[d] or (isQanaiyaq and workGEOL in Oxide[d]):
              workT1 = T1_weathered[d]
              workT2 = T2_weathered[d]
              workT6 = T6_weathered[d]
         else: # exhalite as default
              workT1 = T1_exhalite[d]
              workT2 = T2_exhalite[d]
              workT6 = T6_exhalite[d]

      # TF/ODEN calculation
      if isQanaiyaq:
         if workGEOL in Siksikpuk[d] and not hasMinGrade: # Siksikpuk shale
            TF = Qan_Siksikpuk_Shale_TF
         elif workGEOL in Black_Shale[d] and not hasMinGrade: # general Black Shale
            TF = Qan_Black_Shale_TF
         else:  # grade bearing or not defined
            TF = (TFbase_Q - workPB*PBt_Q - workZN*ZNt_Q - workFE*FEt_Q - workBA*BAt_Q)/Solids_Q
      else: # Main, Aqqaluk, Paalaaq
         if workGEOL in Baritic_Siksikpuk[d] and not hasMinGrade: # Baritic Siksikpuk shale
            TF = Baritic_Siksikpuk_Shale_TF
         elif workGEOL in Siksikpuk[d] and not hasMinGrade: # Siksikpuk shale
            TF = Siksikpuk_Shale_TF
         elif workGEOL in Black_Shale[d] and not hasMinGrade: # general Black Shale
            TF = Black_Shale_TF
         else:  # grade bearing or not defined
            if isPaalaaq: # Paalaaq
               TF = (TFbase_P - workPB*PBt_P - workZN*ZNt_P - workFE*FEt_P - workBA*BAt_P)/Solids_P
            else: # Main or Aqqaluk
               TF = (TFbase_A - workPB*PBt_A - workZN*ZNt_A - workFE*FEt_A - workBA*BAt_A)/Solids_A
      workODEN = round(1.0/TF,5)
      workODENM = round(1.0/TF/1.10231,5)
      SG = round(pow(3.2808,3)* workODENM,2)

      # ORCT1
      if isQanaiyaq:
         if workGEOL in Block_1_Q:
            ORCT1 = 1
         elif workGEOL in Block_2_Q:
            ORCT1 = 2
         elif workGEOL in Block_3_Q:
            ORCT1 = 3
         elif workGEOL in Block_4_Q: #test AR 2-26-24; no downstream call of this variable; just coding now by new flt blocks
            ORCT1 = 4
         elif workGEOL in Block_5_Q:
            ORCT1 = 5   
         else:
            ORCT1 = 6
      else: # Main, Aqqaluk, or Paalaaq
         if workGEOL in Lower_Plate_A:
            ORCT1 = 8
         elif workGEOL in Middle_Plate_A:
            ORCT1 = 1
         elif workGEOL in Sublower_Plate_P:
            ORCT1 = 6
         else:
            ORCT1 = 5

      # ORCT2
      if isQanaiyaq and workGEOL in Oxide[d]:  # because this is set first Weathered below has no Oxide
         ORCT2 = 7
      elif workGEOL in Weathered[d]:
         ORCT2 = 2
      elif workGEOL in Exhalite[d]:
         if workFE < FElimit and workBA < BAlimit:
            ORCT2 = 1
         elif workBA >= BAlimit:
            ORCT2 = 3
         else: # workFE >= FElimit
            ORCT2 = 4
      elif workGEOL in Vein[d]:
         ORCT2 = 8
      elif workGEOL in Baritic[d]:
         ORCT2 = 3
      else: # all others (default for Blasthole data, different for Block Model data)
         ORCT2 = 10

      # mineral percentages for Self Heating Capacity Risk Region and Blasting Agent Reactivity
      Sph = workZN/0.6709 + FEinFeS/0.6352
      Pyr = FEinFeS2/0.4655
      Ang = workSPB/0.6832  # Anglesite
      Bar = workBA/0.5884

      # Self Heating Capacity Risk Region (Nessetech 2016)
      # SHCRR: 1-safe, 2-will not heat >100C, 3-do not expose to high heat, 4-monitor, 5-preventative action required
      # Note: SHCRR 0 and 6 not assigned, as in block model, as all holes should have Zn and Fe assays
      # Clip mineral percentages
      PyrSHC = max(Pyr, 5)
      SphSHC = min(Sph, 48)
      # calculate A, B, and Risk Region
      A = max(-1.33 + 0.0614*PyrSHC + 0.3*SphSHC - 0.00847*pow(SphSHC,2) + 0.0115*PyrSHC*SphSHC,0)
      B = max(-6.56 + 0.896*PyrSHC - 0.00588*pow(PyrSHC,2),0)
      if A < 1 and B < 1:
         SHCRR = 1
      elif A < 1:
         SHCRR = 3
      elif B < 1:
         SHCRR = 2
      elif A < 5 or B < 5:
         SHCRR = 4
      else:
         SHCRR = 5

      # Blasting Agent Reactivity (July 2018 revision to model using 2014 & 2016 data)
      # Note: BRXNF in block model is 1/0/undef, but in OCS model is 2/1/0
      # BRXNF: 0-no reaction, with or without Urea, 1-reaction possible without Urea, 2-reaction possible in blends with Urea
      if workGEOL in SulfideHost[d]:
         Sph_Pyr_defined = Pyr > 0
         if Sph_Pyr_defined:
            Sph_Pyr = Sph/Pyr
         if RPB_defined and Sph_Pyr_defined and (workRPB >= 10 and workRPB <= 95) and Sph_Pyr <= 1.42 and Pyr >= 6.2 and workS >= 0.12:
            # eta AA basis
            eta = min(max(101.2 - 22.6234*Pyr + 7.53677*Ang - 325.38*Sph_Pyr + 43.4091*B,-10.0),10.0) # note that "B" value is from SHCRR calculation
            RXNmax_AA = exp(eta)/(1 + exp(eta))
            # eta XRF basis
            eta = min(max(395.764 - 5.13326*NSG - 21.3756*Bar - 60.4365*Pyr - 9.35528*Sph + 138.797*B - 80.0252*SHCRR,-10.0),10.0)
            RXNmax_XRF = exp(eta)/(1 + exp(eta))
            if RXNmax_AA >= 0.5 or RXNmax_XRF >= 0.5:
               workBRXNF = 2
            else:
               workBRXNF = 1
         else:
            workBRXNF = 0
      else:
         workBRXNF = 0
      # set BA Reaction Flag exception for Ikalukrok shale (due to pyrite inclusions)
      if workGEOL in BA_shale_reactive[d] and workBRXNF != 2: # check BRXNF for mixed shale blocks, tag incase sulfide portion does not exhibit high reactivity from above calculations
         BRXNF = 1  # reaction possible without Urea

      # Set waste segregation criteria WARDC: 0-Possibly Reactive, 1-Non-reactive, 2-Construction, 3-Cover
      Gal = (workPB-workSPB)/0.8660
      totalSulfide = Sph + Gal + Pyr
      if KeyCreek and workZN <= 0.25 and totalSulfide <= 10.0 and workBA < MinGrade: # these are individual hole criteria
         WARDC = 3
      elif (workGEOL in Siksikpuk[d] or workGEOL in Baritic_Siksikpuk[d] or workGEOL in Baritic[d] or workGEOL in Exhalite[d]) and workZN <= 1.0 and workPB <= 1.0 and workFE <= 3.5: # these are individual hole criteria
         WARDC = 2
      elif SHCRR >= 5: # possibly reactive
         WARDC = 0
      else:  # non/low reactivity
         WARDC = 1

      if workGEOL in SulfideHost[d]:  # ore host rock type specific calculations
         # calculate SiO2 values for Qanaiyaq metallurgy and PCA analysis
         if workSIO2 < 0:  # no SiO2 assay, so use calculated value as measured
            SIO2met = NSG
         else:  # SiO2 assay available, so use as measured
            SIO2met = workSIO2

         # calculate ZNFE ratio for PCA analysis
         ZNFE_defined = workFE > 0
         if ZNFE_defined:
            ZNFE = workZN/workFE

         # ---------------------------------------------------------
         # Calculate zinc and lead concentrate grades and recoveries
         # ---------------------------------------------------------

         # set minima to Zn, Pb, Ba, and Fe grades for recovery calcs then recalc SiO2 and Ba
         ZNmet = max(workZN,ZNmin)
         PBmet = max(workPB,PBmin)
         if RPB_defined and workRPB != 0:
            SPBmet = PBmet * workRPB/100.0  # constant ratio
         else:
            if workGEOL in Weathered[d] or (isQanaiyaq and workGEOL in Oxide[d]):
               SPBmet = PBmet * pctRPBweathered[d]
            else:
               SPBmet = PBmet * pctRPBnonweathered[d]
         BAmet = max(workBA,BAmin)
         FEmet = max(workFE,FEmin)
         FEinFeSmet = ZNmet * min(FEmet/ZNmet,FEinZN)
         FEinFeS2met = FEmet - FEinFeSmet
         NSGmet = 100.0 - (ZNmet/0.6709 + (PBmet-SPBmet)/0.8660 + SPBmet/0.6832 + FEinFeS2met/0.4655 + FEinFeSmet/0.6352 + BAmet/0.5884 + workS + workTOC)
         if NSGmet < NSGmin:
            deltaNSG = NSGmin - NSGmet
            NSGmet = NSGmin
            BAmet = max((BAmet/0.5884 - deltaNSG)*0.5884,BAmin)

         # assign MET codes
         if DEP <= 2: # Main or Aqqaluk (these have been simplified from original 5 as only Weathered was extraordinary)
            if not RPB_defined: # waste
               MET = 0
            else:
               if workRPB >= RPBlimit and workSPB >= SPBlimit: # all Weathered by RPB + sPb criteria
                  MET = 2 # Weathered
               else: # remainder; no Oxide or GEOL1 codes in Main or Aqqaluk
                  MET = 1 # Regular
         elif DEP <= 3: # Paalaaq
            if workGEOL in Exhalite[d]:
               if workBA >= BAlimit:
                  MET = 9 ##### Baritic
               else:
                  MET = 7 ##### Exhalite
            elif workGEOL in Vein[d]:
               MET = 8 ##### Veined
            elif workGEOL in Baritic[d]:
               MET = 9 ##### Baritic
            else: # waste/error -> as not defined in above three geology code groupings
               MET = 0 #####Waste
         else: # DEP == 4, Qanaiyaq
            MET1_2RecoveryDeduct = False
            if not RPB_defined: # waste
               MET = 0 ##### Waste
            else:
               if (workRPB >= RPBlimitOX and workSPB >= SPBlimitOX and ZNPB_defined and ZNPB < ZNPBmaxOX): # REMOVED ORCT2==7 possible High Lead-Silver Oxide (lead concentrate) 
                  MET = 3 ##### Oxide
               else:
                  if workRPB < RPBlimit or (workRPB >= RPBlimit and workSPB < SPBlimit): # Regular (zinc & lead)
                     MET = 1 ##### Regular
                  elif workRPB < RPBlimitPB: # i.e. RPBlimit <= RPB < RPBlimitPB
                     if workCU < CUlimitHI: # Regular (zinc & lead)
                        MET = 1 ##### Regular
                        MET1_2RecoveryDeduct = workCU > CUlimitLO # flag True in linear reduction region
                     else:
                        MET = 4 # remaining is Weathered High Copper (bulk concentrate)
                  else: # RPB >= RPBlimitPB
                     if workCU < CUlimitHI: # Weathered (zinc only)
                        MET = 2 ##### Weathered
                        MET1_2RecoveryDeduct = workCU > CUlimitLO # flag True in linear reduction region
                     else:
                        MET = 4 # remaining is Weathered High Copper (bulk concentrate)

         # WXFG and QWXFG (Weathered flag for mill feed; metallurgical, not geological, based definition; weathered = 1, unweathered = 0)
         QWXFG = int(isQanaiyaq and MET >= 2)  # Note: given the copper parameter in Qanaiyaq MET coding, Weathered in Qan has >= RPBlimitPB whereas Weathered in Aqq has >= RPBlimit
         WXFG = max(int(not isQanaiyaq and MET == 2), QWXFG)

         if isQanaiyaq: # DEP == 4, Qanaiyaq
         # conc grades
            ZNGRD = 53.0
            PBGRD = 54.5
            PBGOX = 45.0
            ZNGWX = 40.5
            PBGWX = 7.5

            # zinc concentrate 1
            if MET == 1 or MET == 2: # 1-Regular (zinc & lead), 2-Weathered (zinc)
               AGclip = max(min(workAG,6.912),1.158) # clip AG based on range of data used to develop model
               TOCclip = max(min(workTOC,0.65),0.10) # clip TOC based on range of data used to develop model
               ZZ = 13.78371 + 1.32534*workZN - 1.85221*workSPB + 0.66301*SIO2met + 2.20423*AGclip - 13.85855*TOCclip + 0.21601*workT2
               if MET1_2RecoveryDeduct: # transition area where Cu% between LO and HI and RPB >= RPBlimit
                  CUreduction = max(min(CUlimitInt - CUlimitSlp*workCU,1.0),0.0) # linear reduction to recovery for region between LO and HI limits
                  Z = CUreduction*ZZ
               else:
                  Z = ZZ # as CUreduction = 1.0
                  Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
                  ZNREC = min(max(Z,0),ZnRecMax)
            else:  # no Zn concentrate from MET 3-Weathered (possible non-sulphide process feed) or 4-Weathered High Copper
               ZNREC = 0.0
            # Weathered High Copper
            if MET == 4 or MET1_2RecoveryDeduct:
               Z = 6.67*workZN-33.33 # assume linear relationship; test feed of 17% Zn gave 80% Rec and assume a feed of 5% Zn would give 0% Rec
               Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
               ZNRWX = min(max(Z,0),ZnRecMax)
            else:  # no Bulk concentrate from 1-Regular (zinc & lead), 2-Weathered (zinc), or 3-High Lead-Silver Oxide
               ZNRWX = 0.0 ##### Zn Recovery to Weathered Ore Bulk Conc

            # lead concentrate
            if MET == 1: # 1-Regular (zinc & lead)
               P = round(63.67652 - 11.3144*workSPB + 1.044188*workPB,2)
               PBREC = min(max(P,0),PbRecMax)
            else: # no Pb concentrate from 2-Weathered (zinc), 3-High Lead-Silver Oxide, or 4-Weathered High Copper
               PBREC = 0.0
            # High Lead-Silver Oxide
            if MET == 3:
               if workPB > 0:
                  P = round(67.2*log(workPB) - 104.0,2)  # recovery modelled from data in D.Lin (File Note; Sept 12, 2017)
                  PBROX = min(max(P,0),PbRecPbOxMax)
               else:
                  PBROX = 0.0
            else: # no Oxide concentrate from 1-Regular (zinc & lead), 2-Weathered (zinc), or 4-Weathered High Copper
               PBROX = 0.0
            # Weathered High Copper
            if MET == 4 or MET1_2RecoveryDeduct:
               if workPB > 0:
                  ConcTns = workZN*ZNRWX/ZNGWX
                  P = round(ConcTns*PBGWX/workPB,2)
                  if P <= PbRecMax: # ideally this should balance with zinc metallurgy so should not need a max limit; however, the calculated value was found to go up to 100% so a limit check is required
                     PBRWX = max(P,0)
                  else: # if Pb recovery is clipped then new concentrate Pb grade must be computed at that recovery
                     PBRWX = PbRecMax
                     PBGWX = round(workPB*PBRWX/ConcTns,2)
               else:
                  PBRWX = 0.0
            else: # no Bulk concentrate from 1-Regular (zinc & lead), 2-Weathered (zinc), or 3-High Lead-Silver Oxide
               PBRWX = 0.0
         else: # Main, Aqqaluk, Paalaaq
            if DEP <= 2 or (isPaalaaq and MET == 9): # only for Main, Aqqaluk, and baritic Paalaaq
               ZNGRD = 53.0
               PBGRD = 54.5
               if (workZN == 0 and workPB == 0) or MET == 0: # then skip further Zn and Pb recovery calculations
                  ZNREC = ZnRecMin
                  PBREC = PbRecMin
               else:
                  RPBmet = SPBmet/PBmet * 100.0
                  sulPB = PBmet - SPBmet
                  ZNadjPB = max(11.0692 * exp(-0.0239*workRPB) - 0.5748*sulPB, ZNadjPBmin)
                  PBadjPB = max(4.0118 * exp(-0.0766*workRPB) + 0.5396*sulPB, PBadjPBmin)

                  # zinc concentrate 2
                  if FEmet <= recLimitFE and ZNmet <= recLimitZN and BAmet >= recLimitBA:  # use original ZNREC model as exponential model over-estimates recovery for low Zn, low Fe, high Ba blocks
                     ZNREClab = round(35.8735*pow(ZNmet,0.2504)*pow(PBmet,-0.1601)*pow(FEmet,-0.05875)*pow(NSGmet,0.09152),2)
                     ZNREClab = min(max(ZNREClab,ZnRecMin),ZnRecMax)  # min now 30, was 40 in old URF
                  else:  # use revised, exponential model
                     # limit high BA grades for Aqqaluq Weathered, note SiO2 is not recalculated; also not required in PB conc logic as no PB conc at high RPB
                     if MET == 2: # limit high BA grades for Aqqaluq Weathered, note SiO2 is not recalculated and only MET=9 for Paalaaq here; also not required in PB conc logic as no PB conc at high RPB
                        BAmet = min(BAmet,BAlimitWeathered)
                     # use exponential model
                     e1 = 0.0161 * BAmet + 0.2481
                     e2 = -0.0024 * BAmet - 0.0888
                     e3 = -0.0075 * BAmet + 0.0740
                     e4 = -0.0018 * BAmet + 0.1491
                     e5 = 0.0117 * BAmet + 0.0136
                     e6 = -0.0160 * BAmet + 0.0029
                     e7 = -0.0405 * BAmet + 0.1711
                     # prior to the following eqn, these values should have passed: ZNmet > 0 and PBmet > 0 and SPBmet > 0 and FEmet > 0 and NSGmet > 0 and BAmet > 0 and ZNadjPB > 0
                     ZNREClab = 17.469*pow(ZNmet,e1)*pow(PBmet,e2)*pow(FEmet,e3)*pow(NSGmet,e4)*pow(BAmet,e5)*pow(SPBmet,e6)*pow(ZNadjPB,e7)
                  Y = max(4.60517 - log(ZNREClab),0.0001)
                  if ORCT2 == 3: # Baritic ore type; May 2016 Baritic specific plant transfer function
                     Z = ZNREClab + (10.7349/Y) * exp(-0.5*pow((log(Y)+0.42027)/0.58708,2))
                  else: # April 2003 plant transfer function
                     Z = ZNREClab + (4.0746/Y) * exp(-0.5*pow((log(Y)+0.87774)/0.42255,2))
                  Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
                  ZNREC = min(max(Z,ZnRecMin),ZnRecMax)

                  # lead concentrate 2
                  if MET == 2: # no Pb conc produced for milling criteria weathered Aqqaluk/Main, note that only MET=9 for Paalaaq here
                     PBREC = 0.0
                  else:
                     e1 = 0.0762 * FEmet - 0.3363
                     e2 = -0.3824 * FEmet + 3.6151
                     e3 = 0.000 * FEmet - 0.1788
                     e4 = 0.0410 * FEmet - 0.0603
                     e5 = 0.0075 * FEmet - 0.0419
                     e6 = 0.1602 * FEmet - 1.6041
                     e7 = 0.2504 * FEmet - 2.4251
                     # prior to the following eqn, these values should have passed: ZNmet > 0 and PBmet > 0 and SPBmet > 0 and PBadjPB > 0 and FEmet > 0 and NSGmet > 0 and BAmet > 0
                     PBREClab = round(9.24*pow(ZNmet,e1)*pow(PBmet,e2)*pow(FEmet,e3)*pow(NSGmet,e4)*pow(BAmet,e5)*pow(SPBmet,e6)*pow(PBadjPB,e7),2)
                     PBREC = min(max(PBREClab,PbRecMin),PbRecMax)
            else: # DEP == 3, Paalaaq, and MET == 7 or 8
               if workGEOL in Vein[d]: # MET == 8, Veined, ore Type B
                  ZNGRD = 60.0   # NOTE: v 2.0.0 Strategic Planning changed all ZNGRD values to 53 and all PBGRD to 54.5 but no technical info to support change and no impact on GC
                  PBGRD = 48.8   # NOTE: v 2.0.0 Strategic Planning changed all ZNGRD values to 53 and all PBGRD to 54.5 but no technical info to support change and no impact on GC
                  ZNREC = round(81.3*ZnRec_eff,1)
                  PBREC = 67.0
               else: # MET == 7, Siliceous, ore Type A (or undefined...)
                  ZNGRD = 49.6   # NOTE: v 2.0.0 Strategic Planning changed all ZNGRD values to 53 and all PBGRD to 54.5 but no technical info to support change and no impact on GC
                  PBGRD = 48.6    # NOTE: v 2.0.0 Strategic Planning changed all ZNGRD values to 53 and all PBGRD to 54.5 but no technical info to support change and no impact on GC
                  ZNREC = round(43.8*ZnRec_eff,1)
                  PBREC = 49.6

         # silver grade (grams/tonne) in both zinc and lead concentrates, no differention by deposit
         # Regular, i.e. Main, Aqqaluk, Paalaaq, or Qanaiyaq (sulphide ore MET codes)
         if DEP <= 3 or (DEP == 4 and (MET == 1 or MET == 2)):
            # Ag recovery to Oxide Pb or Bulk concentrates
            AGGOX = 0.0
            # Ag recovery to Zn concentrate
            if workTOC > 0 and ZNREC > 0:  # and FE > 0 and SiO2 > 0
               AgRecZn = min(max(0.71200*exp(-7.416)*pow(FEmet,0.1988)*pow(workTOC,-0.1760)*pow(NSGmet,-0.4080)*pow(ZNREC,2.659) + 19.05360,0.0),AgRecZnMax)
            else:
               AgRecZn = 0.0
            # Ag recovery to Pb concentrate
            if workAG > 0 and PBREC > 0 and not(not isQanaiyaq and workRPB > RPBlimit) and not(isQanaiyaq and MET >= 2): # and PB > 0 and SPB > 0 and not high soluble lead material
               AgRecPb = min(max(0.50950*exp(-4.665)*pow(PBmet,1.459)*pow(SPBmet,-0.5752)*pow(workAG,-1.040)*pow(PBREC,1.517) + 14.41932,0.0),AgRecPbMax)
            else:
               AgRecPb = 0.0
            # cap Ag recoveries based on total recovery
            AgRecTotal = AgRecZn + AgRecPb
            if AgRecTotal > AgRecPbMax:
               AgRecAdjust = AgRecPbMax/AgRecTotal
               AgRecZn = AgRecZn*AgRecAdjust
               AgRecPb = AgRecPb*AgRecAdjust
            # convert Ag recoveries to Ag grades
            if AgRecZn > 0 and workZN > 0 and ZNREC > 0:
               AGGZN = round(AGM*AgRecZn/(workZN*ZNREC/ZNGRD),1)
            else:
               AGGZN = 0.0
            if AgRecPb > 0 and workPB > 0 and PBREC > 0:
               AGGPB = round(AGM*AgRecPb/(workPB*PBREC/PBGRD),1)
            else:
               AGGPB = 0.0
         else: # Qanaiyaq 3-High Lead-Silver Oxide or 4-Weathered High Copper
            # Ag recovery to zinc or lead concentrates
            AGGZN = 0.0
            AGGPB = 0.0
            # Ag recovery to High Lead-Silver Oxide
            if MET == 3 and PBROX > 0 and AGM > 0: # Qanaiyaq High Pb-Ag Oxide exception
               A = 56.8*log(AGM) - 252.8  # from follow-up graph to Sept 12,'17 file note by D.Lin
               AgRecPbOx = min(max(A,0),AgRecPbOxMax)
               AGGOX = round(AGM*AgRecPbOx/(workPB*PBROX/PBGOX),1)
            else:
               AGGOX = 0.0
         # Ag recovery to Weathered High Copper
         if DEP == 4 and (MET == 4 or MET1_2RecoveryDeduct):
            AGGWX = 381.0
            if AGM > 0: # then can check for exception if recovery too high
               ConcTns = workZN*ZNRWX/ZNGWX
               AgRecWx = ConcTns*AGGWX/AGM
               if AgRecWx > AgRecPbMax: # recovery too high so adjust grade
                  AGGWX = round(AGM*AgRecPbMax/ConcTns,1)
         else:
            AGGWX = 0.0

         # -------------------------------
         # Calculate grinding throughput
         # -------------------------------

         # PCA class determination
         Gal = (workPB-workSPB)/0.8660
         Sph = workZN/0.6709 + FEinFeS/0.6352
         Pyr = FEinFeS2/0.4655
         Bar = workBA/0.5884
         U1YP = -0.004074671*Bar + 0.012634782*NSG - 0.025242613*Sph - 0.107611865*Gal - 0.015048441*Pyr - 0.00473548*10*workTOC
         U2XP = 0.03159656*Bar - 0.000326032*NSG - 0.002455592*Sph - 0.014168624*Gal - 0.019183818*Pyr - 0.034004886*10*workTOC
         U = Point(U2XP,U1YP,1)

         # assign PCA class
         universal_Ab = False
         universal_BBMWi = True
         BBMWi = 0.0 # default value
         if PCA3.contains(U): # Baritic
            ACLS = 3
            P80 = P80coarse
            if ZNFE_defined:
               Ab = round(15.18*Gal + 2.054*Bar - 226.1*workTOC - 3.133*ZNFE,1)
            else:
               Ab = Ab_min
            BBMWi = round(14.23 - 0.144*workT2 - 0.0619*workT6 - 0.227*Sph,2)
            universal_BBMWi = False
         elif PCA6.contains(U): # Siliceous
            ACLS = 6
            P80 = P80fine
            Ab = round(71.33 - 0.223*workT6 - 1.049*Pyr + 1.141*Bar,1)
         elif PCA4.contains(U): # Sphalerite
            ACLS = 4
            P80 = P80fine
            Ab = round(27.45 + 0.556*workT2 + 0.638*Sph + 1.179*Bar,1)
         elif PCA7.contains(U) == 1: # Sil-Pyr
            ACLS = 7
            P80 = P80fine
            Ab = round(43.18 + 0.154*workT2 + 0.368*Sph + 3.905*Bar - 6.462*workTOC,1)
         elif PCA8.contains(U) == 1: # Pyr-Sph
            ACLS = 8
            P80 = P80fine
            Ab = round(391.8 - 0.133*workT6 - 1.720*NSG - 74.554*SG,1)
         elif PCA5.contains(U): # Sil-Sph
            ACLS = 5
            P80 = P80fine
            if ZNFE_defined:
               Ab = round(37.06 + 0.562*workT2 + 26.35*workTOC + 0.867*ZNFE,1)
            else:
               Ab = Ab_min
         elif PCA1.contains(U): # Barite Transition
            ACLS = 1
            P80 = P80medium
            universal_Ab = True
         elif PCA2.contains(U) == 1: # Sphalerite Transition
            ACLS = 2
            P80 = P80fine
            universal_Ab = True
         elif PCA9.contains(U) == 1: # Sil-Barite Transition
            ACLS = 9
            P80 = P80medium
            universal_Ab = True
         elif PCA10.contains(U): # High TOC Universal
            ACLS = 10
            P80 = P80fine
            universal_Ab = True
         elif PCA11.contains(U): # High Galena Universal
            ACLS = 11
            P80 = P80fine
            universal_Ab = True
         else: # not defined in any polygons
            ACLS = 0
            P80 = P80fine
            universal_Ab = True

         # calculate Ab
         if universal_Ab or Ab < Ab_min or Ab > Ab_max:  # Universal Ab model for all undefined classes or if out of limits with specific Class-based equation
            if ZNFE_defined:
               Ab = round(38.60 + 0.160*workT2 + 0.469*Sph + 1.295*Bar - 0.647*ZNFE,1)
               Ab = min(max(Ab,Ab_min),Ab_max)
            else:
               Ab = Ab_min
         if QWXFG == 1: # Qanaiyaq Weathered exception for Ab as poor quality rock
            Ab = min(max(150.0, Ab), Ab_max) # for friable material

         # calculate BBMWi
         BBMWi_min = 66.748*pow(Ab,-0.445)
         if isQanaiyaq:
            BBMWi = round(0.49216*workZN + 0.2699*NSG - 0.10428*workT1,2)
         else:  # Main, Aqqaluk, Paalaaq
            if universal_BBMWi or BBMWi < BBMWi_min or BBMWi > BBMWi_max: # use Universal form
               BBMWi = round(5.772 + 0.0256*workT2 + 0.105*NSG + 4.95*workTOC,2)
         BBMWi = min(max(BBMWi,BBMWi_min),BBMWi_max) # ensure limited whether from Class or Universal basis

         # calculate specific energy and throughput
         # --------------------------------------------------------------
         # Function to calculate power, can be used for SAG or Ball mills
         # parameters are: mill type ('SAG' or 'BALL'), Critical Speed (fraction), Ball Charge (fraction), Mill Load (fraction), & mill dimensions (metres): inside radius, inside belly length, center line length, & trunion diameter)
         def Power(mill,CSmill,BCmill,MLmill,mill_radius,mill_belly,mill_center,mill_trunion):
            RPS_CS_fr = CSmill*30/pi*pow(Cgvty/mill_radius,0.5)/60 # revolutions per second at the fraction of Critical Speed mill is being run
            Solids_V_fr = Solids_W_fr/SG/(Solids_W_fr/SG + (1-Solids_W_fr)/SGliquid) # solids volume fraction
            SGslurry = Solids_V_fr*SG - Solids_V_fr + SGliquid
            mill_vol = mill_belly*pi*pow(mill_radius,2) # cubic metres
            MASSballs = BCmill*mill_vol*0.6*SGball
            MASSore = SG*mill_vol*(MLmill*(0.6+0.4*Solids_V_fr) - BCmill*0.6)
            MASSliquid = MLmill*mill_vol*0.4*(1-Solids_V_fr)*SGliquid # 0.004 changed to 0.4 as ML is defined as a fraction not a % in this implementation
            VOLcharge =(MASSore/SG + MASSballs/SGball)/(0.6 + 0.4*Solids_V_fr)
            SGcharge = (MASSballs + MASSore + MASSliquid)/VOLcharge
            t_const = 0.35*(3.364-MLmill) - CSmill
            if t_const < 0:
               t = halfPI
            else:
               t = 2.5307*(1.2796-MLmill)*(1-exp(-19.42*t_const)) + halfPI
            s = halfPI - (t-halfPI)*(0.3386 + 0.1041*CSmill + (1.54 - 2.5673*CSmill)*MLmill)
            ALtemp1 = (2*pi+s-t)/(2*pi)         # Active Load, interim calc #1
            ALtemp2 = pow(1-MLmill/ALtemp1,0.5) # Active Load, interim calc #2
            ALtemp3 = 2*ALtemp1/RPS_CS_fr       # Active Load, interim calc #3
            AL_fract = ALtemp3/(pow(mill_radius*(1+ALtemp2)*(sin(s)-sin(t))/Cgvty,0.5) + ALtemp3) # Active Load fraction
            charge_surface_radius = mill_radius*pow(1-AL_fract*MLmill/ALtemp1,0.5)
            z = pow(1-MLmill,0.4532)
            if t_const < 0:
               kinetic_energy_allowance = 0.0
            else:
               ki_temp = mill_radius - z*charge_surface_radius
               kinetic_energy_allowance = mill_belly*SGcharge*pow(pi*RPS_CS_fr*mill_radius/ki_temp,3)*(pow(ki_temp,4) - pow((1-z)*charge_surface_radius,4))
            if mill == 'SAG': # SAG mills use a grate, Ball mills do not
               t_overflow = t
               overflow_mill_correction_pe = 0.0
            else: # Ball mill
               t_overflow = 3.395
               if t_overflow > t:
                  overflow_mill_correction_pe = 0.0
               else:
                  overflow_mill_correction_pe = 2*pi*Cgvty*mill_belly*SGslurry*RPS_CS_fr*(pow(mill_radius,3)*((1-MLmill)/2 + MLmill/3) - pow(charge_surface_radius,2)*mill_radius*(1-MLmill)/2 - MLmill/3*pow(charge_surface_radius,3))*(sin(t)-sin(t_overflow))
            ConeEnd_const = 4*(mill_center - mill_belly)/(2*mill_radius - mill_trunion)
            ConeEnd_pe_const = pi*RPS_CS_fr*Cgvty*ConeEnd_const*(SGcharge*(sin(s) - sin(t)) + SGslurry*(sin(t) - sin(t_overflow)))
            ConeEnd_pe = ConeEnd_pe_const*(pow(mill_radius,4) - 4*mill_radius*pow(charge_surface_radius,3) + 3*pow(charge_surface_radius,4))/12
            ConeEnd_ke_const = SGcharge*2*ConeEnd_const*pow(RPS_CS_fr*pi,3)
            ConeEnd_ke = ConeEnd_ke_const/20*(pow(mill_radius,5) - 5*mill_radius*pow(charge_surface_radius,4) + 4*pow(charge_surface_radius,5))
            ConeEnd_total = ConeEnd_pe + ConeEnd_ke
            PRnet = pi*Cgvty*mill_belly*SGcharge*RPS_CS_fr*mill_radius*(2*pow(mill_radius,3) - 3*z*charge_surface_radius*pow(mill_radius,2) + (3*z-2)*pow(charge_surface_radius,3))/(3*(mill_radius - z*charge_surface_radius))*(sin(s)-sin(t)) + overflow_mill_correction_pe + kinetic_energy_allowance + ConeEnd_total # net power draw, kW
            PRnl = 1.68*pow((0.33*mill_center + 0.67*mill_belly)*pow(2*mill_radius,2.5)*CSmill,0.82) # no load power, kW
            PRgross = PRnet*Kmill + PRnl # total, kW
            return PRgross;
         # end of power calculation function
         # ---------------------------------
         # determine power draw (kW) for each SAG mill (Note: fraction of CS is calculated for each mill before main program loop)
         PRsag1_2 = Power('SAG',CSsag1_2,BCsag1_2,MLsag1_2,sag_radius,sag_belly,sag_center,sag_trunion);
         PRsag3 = Power('SAG',CSsag3,BCsag3,MLsag3,sag_radius,sag_belly,sag_center,sag_trunion);
         PRtotal = 2*PRsag1_2 + PRsag3
         # determine average over all SAGs
         CS = (2*PRsag1_2*CSsag1_2 + PRsag3*CSsag3)/PRtotal # fraction of Critical Speed
         BC = (2*PRsag1_2*BCsag1_2 + PRsag3*BCsag3)/PRtotal # fraction of Ball Charge (ball filling)
         ML = (2*PRsag1_2*MLsag1_2 + PRsag3*MLsag3)/PRtotal # fraction of Mill Load (total filling)
         DWI = 100.0*SG/Ab # Drop Weight Index
         if gc == 2: # pre-crushing
            F80 = 0.36*pow(DWI,1.18)*CSSconst # mm
            P1in = 5.547*pow(DWI,-0.45)*CSSconst # % (not a fraction)
         else:
            F80 = 0.392*pow(DWI,1.18)*CSSconst # mm
            P1in = 4.343*pow(DWI,-0.45)*CSSconst # % (not a fraction)
         F80 = max(min(F80,F80max),F80min)
         P1in = min(P1in,P1max)
         T80 = k1[gc] +k2*Ab + k3*BBMWi + k4*CS + k5*ML + k6*ML*BC + k7*F80 + k8*P1in + k9*screen_aper # microns
         DWIAB = C1 + C2*F80 + C3*DWI + C4*F80*DWI
         SEsag = Ksag[gc]*pow(SG*DWIAB,n1)*pow(BBMWi,n2)*pow(T80/1000.0,n3) # SAG Specific Energy, kWh/t
         if gc == 1: # using a Pebble Crusher
            Mic_pebble = 317.061*pow(Ab,-1.013) # crusher ore Work Index (also shown as Wic in Excel model)
            Wc_pebble = Mic_pebble*PRpcr_const # Pebble Crusher Specific Energy, kWh/t
            PRpcr_net = TPH_pebble_expected*Wc_pebble # net Pebble Crusher Power
         else: # no Pebble Crusher
            PRpcr_net = 0.0
         TPHsag = (2*PRsag1_2 + PRsag3 + PRpcr_net)/SEsag
         OFS = 4000*pow(14/BBMWi,0.5) # Optimum Feed Size
         if T80 > OFS: # calculate Oversize Feed Factor (OFF) multiplier
            RRR80 = T80/P80 # Reduction Ratio R80
            OFF = (RRR80 + (0.91*BBMWi - 7)*(T80-OFS)/OFS)/RRR80
         else: # set Oversize Feed Factor to 1
            OFF = 1.0
         SEbm = OFF*10.0*BBMWi*(pow(P80,-0.5) - pow(Kbm[gc]*T80,-0.5))
         TPHbm = (PRbm + PRim_net)/SEbm
         TPH = min(TPHsag,TPHbm)
         # grinding circuit efficency adjustment
         if isQanaiyaq and MET >= 3: # limit to highTPH for OX and WX
            TPH = min(TPH*TPH_eff,highTPH)
         else:
            TPH = TPH*TPH_eff
         if TPH < highTPH: # set SAG/BM flag for "normal" throughputs
            SAGFG = (TPHsag <= TPHbm) # if SAG limited then True (1) else if BM limited then False (0)
         else: # do not define when throughput is "high"
            SAGFG = -99 # used for undefined for Vulcan as UNDEF does not exist

         #----------------------------------------------
         # Calculate smelter terms and concentrate value
         #----------------------------------------------
         #=====================================
         # Function to calculate AMR for single metal conc ($/tonne mill feed)
         # parameters are: Conc type (ZN or PB), Feed grade, Conc grade, Conc recovery, Conc Ag grade, Oxidation loss, Price, % Pay, Deduction, Secondary pay, Treatment, Ag deduction, % Ag pay, Ag refine, Freight, Selling
         def AMR_single(concType,Gfeed,Gconc,Rconc,GconcAg,CGreduction,Pricet,Pay,Deduct,ConcPaySec,Tc,DeductAg,PayAg,RefineAg,Freight,Selling):
            CGnet = Gconc/100.0 - CGreduction
            if CGnet > 0:
               ConcShipped = (Gfeed*Rconc)/10000.0 / CGnet
            else:
               ConcShipped = 0.0
            if ConcShipped > 0:
               # calculate produced to sold conc ratio
               if CGreduction > 0:
                  PSratio = CGnet/(Gconc/100.0) # Production/Sold concentrate ratio
                  GconcAgNet = GconcAg * PSratio
                  dewateringPS = dewatering * PSratio
               else:
                  GconcAgNet = GconcAg
                  dewateringPS = dewatering
               # determine payable Ag
               if GconcAgNet > DeductAg:
                  if concType == 'ZN':
                     AginConcPay = (GconcAgNet - DeductAg) * PayAg
                  else: # PB
                     AginConcPay = min(GconcAgNet - DeductAg, GconcAgNet*PayAg)
               else:
                  AginConcPay = 0.0
               # determine concentrate charge, including Ag
               totalTc = Tc + RefineAg * AginConcPay
               # gross concentrate payment, including Ag
               ConcPay = Pricet * CGnet * min(Pay,(CGnet-Deduct)/CGnet)
               grossConcPay = ConcPay + AgPriceg * AginConcPay + ConcPaySec
               # net concentrate payment calculation and conversion from $/t concentrate to $/t ore
               busIntrptIns = BII * (grossConcPay - totalTc)
               buroughTax = NWABTeff *(grossConcPay - totalTc - Freight)
               netConcPay = grossConcPay - totalTc - Freight - Selling - busIntrptIns - buroughTax - dewateringPS - portsite
               AMR = netConcPay * ConcShipped
            else:
               AMR = 0.0
            return AMR;
         # end of single metal AMR calculation function
         #=====================================
         # Function to calculate AMR for a bulk concentrate ($/tonne mill feed)
         def AMR_bulk():
            ZnCGnet = ZNGWX/100.0
            PbCGnet = PBGWX/100.0
            if ZnCGnet > 0:
               ConcShipped = (workZN*ZNRWX)/10000.0 / ZnCGnet
            else:
               ConcShipped = 0.0
            if ConcShipped > 0:
               # as no CG deduction for bulk at this stage, PSratio would be 1, so adjustment (as in single conc above) not implemented, just set to variables
               GconcAgNet = AGGWX
               dewateringPS = dewatering
               # determine payable Ag
               if GconcAgNet > BkDeductAg:
                  AginConcPay = (GconcAgNet - BkDeductAg) * BkPayAg
               else:
                  AginConcPay = 0.0
               # determine concentrate charge, including Ag
               totalTc = BkTc + PbRefineAg * AginConcPay
               # gross concentrate payment, including Ag
               ConcPay = ZnPricet * ZnCGnet * min(ZnPayZn,(ZnCGnet-ZnDeductZn)/ZnCGnet) + PbPricet * PbCGnet * min(PbPayPb,(PbCGnet-PbDeductPb)/PbCGnet)
               grossConcPay = ConcPay + AgPriceg * AginConcPay
               # net concentrate payment calculation and conversion from $/t concentrate to $/t ore
               busIntrptIns = BII * (grossConcPay - totalTc)
               buroughTax = NWABTeff * (grossConcPay - totalTc - BkFreight)
               netConcPay = grossConcPay - totalTc - BkFreight - BkSell - busIntrptIns - buroughTax - dewateringPS - portsite
               AMR = netConcPay * ConcShipped
            else:
               AMR = 0.0
            return AMR;
         # end of bulk concentrate AMR calculation function
         #=====================================
         # calculate Sulphide float AMR for all deposits
         AMRzn = AMR_single('ZN',workZN,ZNGRD,ZNREC,AGGZN,ZnCGreduction,ZnPricet,ZnPayZn,ZnDeductZn,ZnConcPayPb,ZnTc,ZnDeductAg,ZnPayAg,ZnRefineAg,ZnFreight,ZnSell)
         AMRpb = AMR_single('PB',workPB,PBGRD,PBREC,AGGPB,PbCGreduction,PbPricet,PbPayPb,PbDeductPb,PbConcPayZn,PbTc,PbDeductAg,PbPayAg,PbRefineAg,PbFreight,PbSell)
         AMR = AMRzn + AMRpb  # Blasthole script clips AMR minimum to 0, but Block Model script does not

         # if Qanaiyaq also calculate Oxide (Pb conc) and Weathered (Bulk conc) float AMR
         if isQanaiyaq:
            AMR_OX = AMR_single('PB',workPB,PBGOX,PBROX,AGGOX,PbCGreduction,PbPricet,PbPayPb,PbDeductPb,0.0,PbTc,PbDeductAg,PbPayAg,PbRefineAg,PbFreight,PbSell)
            AMR_WX = AMR_bulk()
         else:
            AMR_OX = 0.0
            AMR_WX = 0.0
      else:  # GEOL not in SulfideHost
         MET = 0
         ACLS = 0
         WXFG, QWXFG = 0, 0  # no grades so no metallurgical weathering estimation for these blocks
         ZNGRD, ZNREC, AGGZN = 53.0, 0.0, 0.0 # Zn conc
         PBGRD, PBREC, AGGPB = 54.5, 0.0, 0.0 # Pb conc
         AMR = 0.0
         PBROX, AGGOX = 0.0, 0.0              # Pb-Ag oxide conc
         ZNRWX, PBRWX, AGGWX = 0.0, 0.0, 0.0  # Zn-Cu weathered conc
         AMR_OX, AMR_WX = 0.0, 0.0
         # deposit specific defaults
         if isQanaiyaq: # DEP == 4, Qanaiyaq
            PBGOX = 45.6             # Pb-Ag oxide conc
            ZNGWX, PBGWX = 40.5, 7.5 # Zn-Cu weathered conc
            if workGEOL in Black_Shale[d]:
               # TF = Qan_Black_Shale_TF for computing grinding parameters
               Ab = 42.8 # Ab & BBWWi from AQQ testing Black Shale as no QAN specific samples
               BBMWi = 20.90
               P80 = 60.0 # "P80coarse"
               SEsag = 9.50
               SEbm = 15.89
               TPH = 439.3*TPH_eff # grinding circuit efficency adjustment
               SAGFG = 0 # if SAG limited then True (1)
##            elif workGEOL in Baritic_Siksikpuk[d]:  *** Commented out as Baritic Siksikpuk not separated from Siksikpuk in most recent Qanaiyaq model QAN2016; however, retained should Baritic Siksikpuk reappear
##               # TF = Qan_Baritic_Siksikpuk_Shale_TF for computing grinding parameters
##               Ab = 195.7 # Ab & BBWWi from AQQ testing Baritic Siksikpuk Shale as no QAN specific samples
##               BBMWi = 9.09
##               P80 = 60.0 # "P80coarse"
##               SEsag = 5.62
##               SEbm = 6.69
##               TPH = 896.4*TPH_eff # grinding circuit efficency adjustment
##               SAGFG = 1 # as TPH is > 672 (highTPH) so undefined, but not in Vulcan; if SAG limited then True (1)
            else:
               # TF = Qan_Siksikpuk_Shale_TF for computing grinding parameters
               Ab = 49.4 # Ab & BBWWi from AQQ testing Siksikpuk Shale as no QAN specific samples
               BBMWi = 18.86
               P80 = 60.0 # "P80coarse"
               SEsag = 9.03
               SEbm = 14.0
               TPH = 498.8*TPH_eff # grinding circuit efficency adjustment
               SAGFG = 0 # if SAG limited then True (1)
         else: # Main, Aqqaluk, Paalaaq (as REC = 0 do not need to specify unique Paalaaq concentrate grades)
            PBGOX = 0.0             # Pb-Ag oxide conc
            ZNGWX, PBGWX = 0.0, 0.0 # Zn-Cu weathered conc
            if workGEOL in Black_Shale[d]:
               # TF = Black_Shale_TF for computing grinding parameters
               Ab = 42.8
               BBMWi = 20.90
               P80 = 60.0 # "P80coarse"
               SEsag = 11.56
               SEbm = 15.88
               TPH = 413.9*TPH_eff # grinding circuit efficency adjustment
               SAGFG = 1 # if SAG limited then True (1)
            elif workGEOL in Baritic_Siksikpuk[d]:
               # TF = Baritic_Siksikpuk_Shale_TF for computing grinding parameters
               Ab = 195.7
               BBMWi = 9.09
               P80 = 60.0 # "P80coarse"
               SEsag = 5.60
               SEbm = 6.78
               TPH = 958.9*TPH_eff # grinding circuit efficency adjustment
               SAGFG = 1 # as TPH is > 672 (highTPH) so undefined, but not in Vulcan; if SAG limited then True (1)
            else:
               # TF = Siksikpuk_Shale_TF for computing grinding parameters
               Ab = 49.4
               BBMWi = 18.86
               P80 = 60.0 # "P80coarse"
               SEsag = 10.32
               SEbm = 14.0
               TPH = 468.5*TPH_eff # grinding circuit efficency adjustment
               SAGFG = 1 # if SAG limited then True (1)

      # Assign DEST => High Grade class: 1-Mill Feed
      #                Low Grade classes: 2-Non-reactive, 3-Possibly Reactive
      #                Waste classes: 4-Possibly Reactive, 5-Non-reactive, 6-Construction, 7-Cover
      #                Other classes: 8-Oxide High Pb-Ag, 9-Weathered High Zn-Cu
      #                Medium Grade classes: 10-Non-reactive, 11-Possibly Reactive

      # calculate operating cost escalators and base operating cost ($/t)
      TPS = TPH / 3600.0
      powerEsc = (SEsag + SEbm - averagePower) * powerCost  # grinding power cost escalator, (+) is increased cost
      throughputEsc = comminutionCost[d]*(averageTPH[d]/TPH - 1)  # throughput rate cost escalator, (+) is increased cost
      haulEsc = max((haulIncrElev[d] - workELEV)/25 * -haulIncrLU, (haulIncrElev[d] - workELEV)/25 * haulIncrLD)  # haulage cost adjustment above/below median bench (either direction an increase); (+) is increased cost
      OpCost_mill_noTails = haulEsc + (mill_cost[d] + powerEsc + throughputEsc) + indirect_cost/TPH

      # calculate Sulphide operating cost and Mill cutoff ($/t)
      ZnConcentrate = (workZN * ZNREC / ZNGRD)/100.0
      PbConcentrate = (workPB * PBREC / PBGRD)/100.0
      tails_cost = (1 - ZnConcentrate - PbConcentrate) * tailsCostPerTonne
      OpCost_mill_SU = OpCost_mill_noTails + tails_cost
      MillCO_SU = OpCost_mill_SU + mine_ore_cost[d] - mine_waste_cost[d]

      # calc NET and VALS
      NET = AMR - OpCost_mill_SU - mine_ore_cost[d] # NET includes mining cost
      NET_RH = NET - rehandle_cost
      VALS = (AMR - MillCO_SU) * TPS  # $/sec for block for direct mill feed, DOES NOT include mining cost, only waste/ore mining differential cost
      VALS_RH = VALS - rehandle_cost * TPS  # $/sec for block for stockpiled LG as includes rehandle

      if VALS >= DPScutoff:
         DEST = HG
      elif VALS >= DPScutoffMG:
         if isQanaiyaq or workFE >= 14 or workBA >= 9: # send direct to the mill if from: i. Qanaiyaq and ii. Aqqaluk if high BA or FE grade (9% Ba gives 85% of tonnage, 14% Fe gives 91% of tonnage)
            DEST = HG
         else:          # send to MGO stockpile, but differentiate N and PR
            if SHCRR < 5:
               DEST = MG_N
            else:
               DEST = MG_PR
      elif VALS >= DPScutoffLG:
         if SHCRR < 5:  # all N goes to LGO stockpile
            DEST = LG_N
         else:          # PR destination for Qan is waste (LG-PR), but Aqq is to mill feed (HG)
            if isQanaiyaq:
               DEST = LG_PR
            else:
               DEST = HG
      elif VALS_RH >= 0:
         if SHCRR < 5:
            DEST = LG_N
         else:
            DEST = LG_PR
      elif WARDC <= 0:
         DEST = W_PR
      elif WARDC <= 1:
         DEST = W_N
      elif WARDC <= 2:
         DEST = W_CN
      else: # WARDC <= 3:
         DEST = W_CV

      # default values ro use for cases of OX or WX when AMR is zero, i.e. no concentrate produced thus 1:1 "ore":tailings tonnage ratio
      OpCost_mill_allTails = OpCost_mill_noTails + tailsCostPerTonne + rehandle_cost
      OpCost_mine_allTails = OpCost_mill_allTails + mine_ore_cost[d]
      OpCost_mill_allTails_VALS = (OpCost_mine_allTails - mine_waste_cost[d]) * TPS
      # check for Ox and Wx exceptions to sulphide feed in Qanaiyaq
      if isQanaiyaq and (DEST >= 3 and DEST <= 7):# vs. no DEST constraint if an OX/WX mill existed vs. DEST >= 5 if policy was to stockpile only non-reactive material (OX is moot, but WX is about 50/50 PR/N)
         # 1) check if Oxide High Lead-Silver
         # calculate tailings tonnage and cost
         PbConcentrate = (workPB * PBROX / PBGOX)/100.0
         tails_cost = (1 - PbConcentrate) * tailsCostPerTonne
         # calculate Oxide operating cost and and Mill cutoff ($/t), include rehandle cost as assume majority will be stockpiled due to: a) small mill size or b) end-of-life milling
         OpCost_mill_OX = OpCost_mill_noTails + tails_cost + rehandle_cost + mill_oxide
         MillCO_OX = OpCost_mill_OX + mine_ore_cost[d] - mine_waste_cost[d]
         # calc NET and VALS
         NET_OX = AMR_OX - OpCost_mill_OX - mine_ore_cost[d]  # $/t, includes mining cost
         VALS_OX = (AMR_OX - MillCO_OX) * TPS                 # $/sec, DOES NOT include mining cost, only waste/ore mining differential cost

         if VALS_OX >= 0:  # then assign to Oxide High Pb-Ag directly as no overlap with regular Sulfide Mill feed
            DEST = SP_OX
            OpCost_mill_WX = OpCost_mill_allTails
            NET_WX = -OpCost_mine_allTails
            VALS_WX = -OpCost_mill_allTails_VALS
         else:
            # 2) check if Weathered High Zinc-Copper
            #    Note: as there is overlap with regular Sulfide Mill feed, the transfer to Weathered can be based on either case below and is set in the constants at top of script:
            #          a) only if Sulfide Milling of the material does not provide a positive cash flow, OR
            #          b) if Weathered Milling provides the greater cash flow of the two choices
            #    Note also that the TPH has been limited for Met=4 when calculated, thus this will reflect in the valuation of this material whether sent to the sulfide or the weathered mill.
            # calculate tailings tonnage and cost
            ZnConcentrate = (workZN * ZNRWX / ZNGWX)/100.0 # Zn basis for Bulk Conc
            tails_cost = (1 - ZnConcentrate) * tailsCostPerTonne
            # calculate Weathered operating cost and Mill cutoff ($/t), include rehandle cost as assume majority will be stockpiled due to: a) small mill size or b) end-of-life milling
            OpCost_mill_WX = OpCost_mill_noTails + tails_cost + rehandle_cost
            MillCO_WX = OpCost_mill_WX + mine_ore_cost[d] - mine_waste_cost[d]
            # calc NET and VALS
            NET_WX = AMR_WX - OpCost_mill_WX - mine_ore_cost[d]  # $/t, includes mining cost
            VALS_WX = (AMR_WX - MillCO_WX) * TPS                 # $/sec, DOES NOT include mining cost, only waste/ore mining differential cost
            if VALS_WX >= 0: # then possiblity exists to assign as Weathered High Zn-Cu
               # NOTE: Stockpiling both Possibly Reactive and Non-reactive material yet WX is about 50/50 PR/N.  Would need to include WARDC if filtering PR/N, i.e. DEST >= W_N (not DEST >= LG_PR) in selection criteria below
               makeWX = DEST >= LG_PR and DEST <= W_N # default: transfer to Weathered Milling if Sulfide Milling does not provide a positive cash flow
               if maximizeWX: # then additionally transfer to Weathered if provides a higher cash flow than Sulfide Milling
                  makeWX = makeWX or (DEST == LG_N and VALS_WX > VALS_RH) or ((DEST <= HG or DEST >= MG_N) and VALS_WX > VALS)
               if makeWX:
                  DEST = SP_WX
                  MET = 4 # reset MET to method it will be processed for clarity output
      else: # Main, Aqqaluk, Paalaaq
         OpCost_mill_OX = OpCost_mill_allTails + mill_oxide
         NET_OX = -OpCost_mine_allTails - mill_oxide
         VALS_OX = -OpCost_mill_allTails_VALS - mill_oxide * TPS
         OpCost_mill_WX = OpCost_mill_allTails
         NET_WX = -OpCost_mine_allTails
         VALS_WX = -OpCost_mill_allTails_VALS

      # ORCT4 code
      if DEST >= LG_N: #  all classes except Direct Mill Feed
          ORCT4 = DEST + 18 # e.g. LG_N=2 becomes ORCT4=20, etc
      elif workZN < 15: # low zinc grade
         if ORCT2 <= 1: # Exhalite
            ORCT4 = 1
         elif ORCT2 <= 2: # Weathered
            ORCT4 = 4
         elif ORCT2 <= 3: # Baritic
            ORCT4 = 7
         elif ORCT2 <= 4: # Iron-rich
            ORCT4 = 10
         else: # ORCT2 = 8, Veined
            ORCT4 = 13
      elif workZN >= 25: # high zinc grade
         if ORCT2 <= 1: # Exhalite
            ORCT4 = 3
         elif ORCT2 <= 2: # Weathered
            ORCT4 = 6
         elif ORCT2 <= 3: # Baritic
            ORCT4 = 9
         elif ORCT2 <= 4: # Iron-rich
            ORCT4 = 12
         else: # ORCT2 = 8, Veined
            ORCT4 = 15
      else: # medium zinc grade
         if ORCT2 <= 1: # Exhalite
            ORCT4 = 2
         elif ORCT2 <= 2: # Weathered
            ORCT4 = 5
         elif ORCT2 <= 3: # Baritic
            ORCT4 = 8
         elif ORCT2 <= 4: # Iron-rich
            ORCT4 = 11
         else: # ORCT2 = 8, Veined
            ORCT4 = 14

      # calculated values fro reporting, not used in script
      TonnesPerBlock = workVOL * workODENM
      GNDHR = round(TonnesPerBlock / TPH,2)
      MPT = round(60.0/TPH,6)

      # write all data to block model
      block["pitph"] = refm.get("PITPH") # need for Accounting
      block["bench"] = workELEV
      block["geolchk"] = geolChange
      block["geol"] = workGEOL
      if replace_PB:
         block["pb"] = workPB
      block["s"] = workS
      block["toc"] = workTOC
      block["ag"] = workAG  # write AG back whether estimated or original
      block["agm"] = AGM
      block["t1"] = workT1
      block["t2"] = workT2
      block["t6"] = workT6
      block["rpb"] = workRPB
      block["nsg"] = NSG
      block["odenm"] = workODENM
      block["oden"] = workODEN
      block["tonnes"] = TonnesPerBlock
      block["brxnf"] = workBRXNF
##      block["qwxfg"] = QWXFG  # not in this script previously
##      block["wxfg"] = WXFG    # not in this script previously
      block["met"] = MET
      block["znrec"] = ZNREC
      block["zngrd"] = ZNGRD
      block["pbrec"] = PBREC
      block["pbgrd"] = PBGRD
      block["aggzn"] = AGGZN
      block["aggpb"] = AGGPB
##      if isQanaiyaq: # for Oxide Pb-Ag and Weathered Zn-Cu
##         block["aggox"] = AGGOX # not in this script previously
##         block["pgrox"] = PBROX # not in this script previously
##         block["pggox"] = PBGOX # not in this script previously
##         block["aggwx"] = AGGWX
      block["zngwx"] = ZNGWX # not in this script previously
      block["pbgwx"] = PBGWX # not in this script previously
      block["znrwx"] = ZNRWX
      block["pbrwx"] = PBRWX # not in this script previously
      block["acls"]  = ACLS
      block["p80"] = P80
      block["ab"] = Ab
      block["bbmwi"] = BBMWi
      block["sesag"] = SEsag
      block["sebm"] = SEbm
      block["sagfg"] = SAGFG
      block["mpt"] = MPT    # similar to below
      block["tph"] = TPH    # similar to above, not saved in Block Model as no good for weighted average calculation
      block["gndhr"] = GNDHR
      block["orcls"] = DEST  # same as below
      block["destc"] = DEST  # same as above
      block["orct1"] = ORCT1
      block["orct2"] = ORCT2
      block["orcat"] = ORCT4  # same as below
      block["orct4"] = ORCT4  # same as above
      # assign REV as sulphide milling AMR (as per historical usage).  Assign NETT and VALS to be for mill feed as per feed type to that specific mill: Sulphide, Oxide, or Weathered, i.e. nothing assumed as waste.
      # this usage of NET is different from in the block model where the NET assignment is a further function of the block destination, i.e. ore or waste
##      block["opcost_base"] = OpCost_base      # different construction in new model, was: OpCost_base = (mine_ore_cost[int(d)] + haulEsc) + (mill_cost[int(d)] + powerEsc + throughputEsc) + indirect_cost/TPH # $/t
      block["opcost_base"] =  mine_ore_cost[d] + OpCost_mill_noTails # !!! note no tailings disposal cost in this parameter !!!!
##      block["opcost_s"] = OpCost_s            # different construction in new model, was: OpCost_s = OpCost_base + tails_cost
      block["opcost_s"] = mine_ore_cost[d] + OpCost_mill_SU # tailings cost included here

      block["rev"] = AMR  # same as below
      block["valt3"] = AMR # same as above
      if DEST == LG_N or DEST == LG_PR: # Low Grade, assuming both Non-reactive and Possibly Reactive (if stockpiled) would have rehandle cost
         block["nett"] = NET_RH
         block["vals"] = VALS_RH
      else:
         block["nett"] = NET
         block["vals"] = VALS
##      if isQanaiyaq: # for Oxide Pb-Ag and Weathered Zn-Cu
##         block["nettox"] = NET_OX
##         block["valsox"] = VALS_OX
##         block["nettwx"] = NET_WX
##         block["valswx"] = VALS_WX
      block["pbcon"] = PbConcentrate*TonnesPerBlock
      block["zncon"] = ZnConcentrate*TonnesPerBlock
print("Block model coding complete")

