#==============================================================================
# Program to perform classification and calculations on model data (e.g. geology ORCT codes, metallurgical parameters, etc.)
#==============================================================================

import sys
from Tkinter import *
import tkMessageBox
from math import *
from datetime import datetime
import getpass

from grail.widgets import *
from grail.rtv import *
import grail.compass.projectinfo
from grail.data import model
from grail.dialogs import gselectprojectdialog
from grail.compass.responsevar import ResponseVar
from grail.compass import cmpsys
from grail import messages
from grail import fileutils
from grail import gsys
from grail.ag import *  # for PCA

#==============================================================================
# Version Information
#==============================================================================

PROC_TITLE = "Model Calculations - ver 24.52.7_QAN - Feb 26, 2024"

# Aug  3, 2010 - v1
# Oct 10, 2010 - v2: added low & high sulphide waste catagories
# Dec  6, 2010 - v3: added minima for BA and FE in met calcs. and readjust BA so mineralization = 100%
# Dec 27, 2010 - v4: added output for AxB and BBMWi grinding parameters
# Jun 30, 2011 - v5: changed REACT calculation from CANMET to NESSETECH regression
# Jul 26, 2011 - v6: readjust SPB so always <= PB, added minima for ZN and PB in met calcs
# Oct  6, 2011 - v7: added criteria for REACT and REASS codes based on ORCT2 for undefined grade blocks
# Mar 20, 2012 - v8: added minimum RPB ratios (10th percentile, low grade) by orebody to lower bound SPB for met calcs
# Aug  2, 2012 - v9: added logic for Resource Classification code (RESCL) and to calculate Zn and Pb conc and tailings tonnages and grinding time
# Dec 22, 2012 - v10: Added GEOL codes 14, 32, 33; changed Paalaaq start row to 144 for new model size; altered Sulphide host checking for REACT
# Feb 10, 2013 - v11: Added GEOL codes 22, 23, 24 for Qanaiyaq weathered exhalite
# Sept 6, 2013 - v12: Added "Veined" types to Qanaiyaq
# Feb 24, 2014 - v13: Updated Qanaiyaq metallurgical recovery and BBMWi formula coding
# June 19, 2014 - v14: Added new SiO2m (measured) model item; added sPB adjustment to TF calculation and revamped TF calculation parameters; added sPB and FE in Sphalerite to mineral percentage calculations;
#                      added GEOL code 33 to Cover classification; clipped total of ZN and PB concs silver Recovery at maximum AGRPB value; increased limit for TPH from 550 to 600;
#                      removed Topo adjustment for PBconc, ZNconc, and GNDHR items; re-incorporated Class-based calculation of Ab; grinding P80 changed from 63 to 70 um;
#                      updated RPB fractions for missing sPB values; changed BBMWi limits from 3 & 30 to 8 & 21; added constant Ab of 150 for QAN weathered; added user selection for assay change
# Nov 28, 2014 - v15: Removed STZNPB_defined boolean for STSPB; renamed SPB_not_defined boolean to STSPB_not_defined; added code for STSPB to be calculated from DDH data RPB if missing in BLASTHOLE data;
#                     fixed double ZNmin (Recovery & MET assignment); added TF modification for waste dumps on Qanaiyaq; added MET code and logic for "High Ag-Low Zn" material in Qanaiyaq;
#                     added STZNPB_defined check in metallurgical recovery; allowed REASS, ZNFE, ZNPB, and RPB to be undefined; added code for old ZNREC model for low ZN, low FE, high BA blocks as recovery overestimated with exponential equation form;
#                     changed WARDC to be based on REACT instead of REASS;
# Dec 20, 2014 - v16: Increased maximum limit for TPH from 600 to 1000 (unlimited); reduced BBMWi lower limit back to 3; assign values to non-Sulphide float parameters in Aqqaluk model; grinding P80 now set by PCA class;
# Feb 7, 2015 - v17: Added GEOL code 50, "air", to Black_Shale group and Paalaaq codes 20 & 34, "Sub-lower Plate Zn>15%" to SulphideHost group; added block size finder for smaller block size models; added Weathered exception for Ab (=150) in Qaniayaq;
#                    incorporated class-based BBMWi calculation for "Baritic" class; added default values to non-sulpide host rock throughput parameters due to incorporation of dilution into block model; removed RESCL coding as not used
# Feb 20, 2015 - v18: Added Weathered exception of BBMWi>=10 in Qaniayaq; removed REASS calculation; revised TF equations for Qanaiyaq (removed outliers)
# May 4, 2015 - v18a: Changed "Cover" criteria to Key Creek material
# June 12, 2015 - v19: Added blasting reagent-rock reactivity coding
# Oct 11, 2015 - v20: Added GEOL code 34;
# Nov 20, 2015 - v21: modified to use MPT (minutes-per-tonne) instead of TPH (tonnes-per-hour);
# Mar 24, 2016 - v22: Ab limit for Qan weathered modified to 150 "or greater" from 150 constant; added code to calculate blended TF and metal grades in waste dumps; revised NS recovery equation for Qanaiyaq oxide;
#                     reworked "first pass on new block model" logic; added Grinding Constraint flag (GCFG); revised GEOL code for waste dumps to be majority based and use default geology code;  added replacement for SPB if greater than PB;
#                     included adjustment of SIO2M (and BA) in Qanaiyaq based on krieged DDH assays and equal % adjustment (previously BA first, SIO2M second); renamed Non-Sulphide items to Oxide; replace TFM with ODENM;
#                     rounded output grade and ratio items; moved GNDHR to Dest script for consistancy with conc; revised Ag recovery equations as predicting too low;
# May 7, 2016 - v22a: upped SAG power from 4540 to 4840 kW and altered P80 suite from 70/77.5/85 to 70/72.5/75 to compensate; changed Zn recovery transfer function to incorporate Baritic (ORCT2=3) specific version;
#                     revised Grinding Constraint flag (GCFG) to only tag lower TPH blocks;
# May 10, 2016 - v22.02: added Paalaaq specific TF equation; changed Paalaaq recovery assignment basis from geographic to geologic (Siliceous, Veined, Baritic); added text log file for script execution;
# Dec 4, 2016 - v22.03: moved Date-Time stamp to top of text output and added user name; altered P80 suite from 70/72.5/75 to 70/77.5/85 ("T" version, more optimistic match for 2014 & 15)
# Feb 16, 2017 - v23.00: revised TF calculation model & parameters; added P80 output; added ORCT1 assignment; added texture defaults for Ab and BBMWi calcs (T1,T2,T6); max BBMWi raised from 21 to 24 kWh/t; added MET=4 for Qanaiyaq high Cu;
#                        replaced min BBMWi limits with equation f(Ab); added Radio Button option for VIP in/out;
# Mar 6, 2017 - v23.50: changed grinding calculation model to TK's 2016 revision (with SAG power calculation); renamed SPNRG to SESAG and added SEBM (was "ODEN"); added SG (was "TF"); renamed GCFG to SAGFG; removed pit slope coding to new script;
#                       revised pre-VIP2 grinding model parameters to best match of actual 2014 & 2015 data: 1) P80 suite from 70/77.5/85 to 64/77/90, 2) RPM for Sag1/2 from 230 to 214 and Sag3 from 230 to 215,
#                       3) BC for Sag1/2 from 0.098 to 0.115 and Sag3 from 0.140 to 0.135, and 4) ML for Sag1/2 from 0.216 to 0.259 and Sag3 from 0.250 to 0.190; lowered post-VIP2 (TK2016) grinding model RPM for all SAGs to 225 from 235
#                       (other items as per TK2016 model, i.e. all SAGs P80 is 60/60/60, BC is 0.140, and ML is 0.254);
# Mar 10, 2017 - v23.51: change Qanaiyaq recovery equations to 55% Zn and 54% Pb grade concs;
# June 2, 2017 - v23.51.01: added TOPO replacement step in initial pass; added ORCT4 calculation (instead of ORCT3); renamed (correctly) SIO2 to NSG and SIO2M to SIO2; ensure NSG set to 100% for shales in initial pass was undef;
# July 1, 2017 - v23.51.02: added filter for computation to only apply to PERLT < 1 (i.e. UNDEF or 0); removed Debug coding;
# July 23, 2017 - v23.51.03: added GEOL code 19 to groups (higher iron version of GEOL code 8);
# Feb 11, 2018 - v24.00: removed CU parameter from PB conc recovery formula in Qanaiyaq; converted conc AG recovery into AG grade computation & renamed model items AGRZN->AGGZN, AGRPB->AGGPB, & AGROX->AGGOX;
#                        added non-Weathered-High RPB in Qanaiyaq to ORCT2 = 7; updated high PB-AG Oxide recovery equations for Pb and Ag; added recovery formulae for Weathered High Copper; added TPH logic for (3) new Qanaiyaq default shales;
#                        added Qanaiyaq Weathering flag QWXFG; Qanaiyaq Cu limit changed from a hard 0.25 to a scaled basis between a LO and HI Cu limit(required rework of recovery logic);
#                        updated reactivity equation to 2016 A/B model & removed Marcasite calc as not well correlated;
#                        => moved topo adjustment, TF calculation, and Ba & sPb revision to new Model_Release script;
# [Mar 25, 2018]         updated blasting reagent-rock reactivity coding based on 2014 and 2016 data;
# [Apr 4, 2018]          moved ORCT4 assignment out to DEST script;
# [June 2, 2018]         added "Failed!" to output text file if run incomplete;
# [July 9, 2018]         moved GNDHR calculation back from DEST script; renamed REACT item SHCRR to prevent confusion with blasting reactivity;
# [Aug 14, 2018]         renamed REACT item SHCRR to prevent confusion with blasting reactivity;
# [Oct 17, 2018]         replaced YEAR with PERLT as MSSO periods of variable size;
# Jan 31, 2019 - v24.40: revised blasting reagent-rock reactivity coding from rework of 2014 and 2016 data;
#                        removed GEOL codes 9, 17, 19, 30, 31, and 34 as no longer used, changed code for Air from 50 to 0, and changed groupings to 2D arrays by deposit; removed CoverType GEOL group as KeyCreek flag made it redundant;
#                        modified WARDC=2 to accept: i) all Construction rock, GEOL 3 & 4 as they have no grades, and ii) grade criteria acceptable Exhalite and Baritic rock;
# Jan 31, 2019 - v24.40.1: set GEOL groups to new QAN2016 model codes and created 2D arrays by deposit
# Feb 15, 2019 - v24.50: added GEOL1 for Qanaiyaq weathered geology and altered ORCT2 logic as a consequence; added WXFG code; simplified MET for Aqqaluk to two codes, Regular and Weathered (from five);
#                        added RPB and SPB limits to existing ZNPB limit for Qanaiyaq Oxide MET criteria; changed sPb and T1/T2/T6 defaults to QAN2016 model;
# Apr 6, 2019 - v24.51: added SHPCT (Shale Percent in mixed composition blocks) and replaced test "if workGEOL in SulfideHost[d]" with "if isSulfide";
#                       moved QWXFG and WXFG into "isSulfide" and "not isSulfide" coding to allow inclusion of grade based weathering classification;
# May 17, 2019 - v24.51.1: P80 of 65um for 5-Year plan (July 2019)
# [June 3, 2019]           removed use of clipped Pyrite and Sphalerite, required for SHCRR calculation, to unclipped versions for BRXNF calculation
# Feb 17, 2020 - v24.52: removed "Construction" and added "Siksikpuk" geology group; removed pre-VIP2 option coding; simplified coding for WXFG, QWXFG, and BRXNF;
# Feb 25, 2020 - v24.52.1: added efficency for TPH and Zn Recovery (all concentrates);
# Mar 28, 2020 - v24.52.2: redefined highTPH upper limit to 5.5Mt/yr (672 tpoh) and set limit for Oxide Pb-Ag and Weathered Zn-Cu;
# Oct 30, 2020 - v24.52.3: changed QWXFG setting based on RPB and workSTSPB limits to MET=2 (thus Weathered Met not exactly same criteria between Aqq and Qan);
# Feb 28, 2021 - v24.52.3a: uses Race21 PTV500 vs. PTV150 initiatives;
# Jan 18, 2022 - v24.52.4: Temporary version with changes to Paalaaq recovery assumptions. Updated recovery for Paalaaq MET=7 and MET=8 to use the same recovery formula as Aqqaluk. Changed Zinc Con Grade to 53%, Pb Con Grade to 54.5% for all met/all deposits
# Feb 16, 2022 - v24.52.5: Restored the original Paalaaq recovery assumptions
# Jan 10, 2023 - v24.52.7: Updated the values for the LOM 2024, planning cycle. Note that the v24.52.6 is the new QAN model update version, with updated geological codes (In Progress). 
# July 3, 2023 - v24.52.7: Same version used for the 5YBP 2024 as there is no change in the metallurgical parameters from LOM to 5YBP
# Feb 26, 2023 - v23.52.7_QAN: update Geol codes for QAN22v6 (updated S) model

#==============================================================================
# Constants
#==============================================================================

# items to get from/put into model
itemlist = ["PERLT","P80","PB","SPB","STZN","STPB","STSPB","STFE","STBA","TOC","S","AG","AGM","NSG","SIO2","GEOL","GEOL1","ORCT1","ORCT2","CU","DEP","ODENM","SG","RPB","ZNFE","ZNPB","MET","ZNGRD","ZNREC","PBGRD","PBREC","AGGZN","AGGPB","ACLS","SESAG","SEBM","MPT","GNDHR","SAGFG","T1","T2","T6","SHCRR","WARDC","AB","BMWi","KCFLG","BRXNF","AGGOX","PBROX","PBGOX","AGGWX","ZNGWX","PBGWX","ZNRWX","PBRWX","QWXFG","WXFG","SHPCT","GEOSM"]
# *** Note: add "FLAG1" to 'itemlist' to tag ore polygon cuts for annual mill throughput Back Calculation

# GEOL code group for plates, ORCT1
Block_1_Q = [11,21,31,41,51,61] # QAN [Exhalite High Grade, Exhalite Low Grade, High-Pb Weathered, Exhalite High Iron, Exhalite High Barium,Exhalite Low Barium]
Block_2_Q = [12,22,32,42,52,62] # QAN [Exhalite High Grade, Exhalite Low Grade, High-Pb Weathered, Exhalite High Iron, Exhalite High Barium,Exhalite Low Barium]
Block_3_Q = [13,23,33,43,53,63] # QAN [Exhalite High Grade, Exhalite Low Grade, High-Pb Weathered,Exhalite High Barium]
Block_4_Q = [14,24,34,44,54,64] # QAN added for the new model
Block_5_Q = [16,26,36,46,56,66] # QAN added for the new model , all undefined will make ORCT1=6
Middle_Plate_A = [1, 6, 11, 15]
Lower_Plate_A = [2, 8, 12, 13, 14, 16, 18]
Sublower_Plate_P = [7, 10, 20, 21]

# geology code group for block model ORCT2, MET, and WARDC (2D array is [M,A,P,Q])
Air = 0
Exhalite = [[1, 8, 11, 18], [1, 8, 11, 18], [20, 21], [10,11,12,13,14,16,20,21,22,23,24,26,40,41,42,43,44,46,60,61,62,63,64,66]] # ORCT2, Aqqaluk and Paalaaq MET, and WARDC, QAN LIST includes Vein unit 110 and 120
Vein = [[6, 13, 14], [6, 13, 14], [10], [110,120]]                     # ORCT2 and Aqqaluk and Paalaaq MET
Baritic = [[15, 16], [15, 16], [7], [50,51,52,53,54,56]]        # ORCT2, Aqqaluk and Paalaaq MET, and WARDC #QAN List [Exhalite High Barium (51,52,53)]
Baritic_Siksikpuk = [[3], [3], [3], []]                         # ORCT2, WARDC, and for setting default values in waste blocks
Siksikpuk = [[4], [4], [4], [200,207]]                              # ORCT2, WARDC, and for setting default values in waste blocks # QAN List [Siksikpuk 200]
Black_Shale = [[25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [201, 202, 203]] # QAN List, Black shale comprises of [Ikalukrok, Kivalina,Basal Melange (201,202,203)]
Weathered = [[2, 12], [2, 12], [], [80,81, 82, 83,84,86,100, 101, 102, 103,104,106]] # ORCT2 and Aqqaluk MET {QAN codes are in GEOL1} # QAN List [Weathered Exhalite (81,82,83), High Weathered Copper (101,102,103)]
Oxide = [[], [], [], [30,31,32,33,34,36]]                       # ORCT2 and Qanaiyaq MET # QAN List [High Pb Weathered (30s coded in GEOL1)]
BA_shale_reactive = [[26], [26], [26], [201]]                   # BRXNF exception for Ikalukrok shale # QAN List [Ikalukrok (201)]

# Block model minimum grades and ratios for calculations
NSGmin, ZNmin, PBmin, BAmin, FEmin, FEinZN  = 0.5, 0.1, 0.1, 0.1, 1.0, 0.035/0.6709 # % FEinZN assumes 3.5% Fe in Sphalerite
pctRPBnonweathered = [0.19, 0.19, 0.19, 0.32]       # %  mean/median of all non-Weathered in pit > breakeven c/o, based on DEP code [Main, Aqqaluk, Paalaaq, Qanaiyaq]
pctRPBweathered = [0.61, 0.61, 0.61, 0.51]          # %  mean/median of all Weathered in pit > breakeven c/o, based on DEP code [Main, Aqqaluk, Paalaaq, Qanaiyaq]

# Grade based ORCT2 assignment limits
BAlimit, FElimit, RPBlimit, SPBlimit = 7.0, 8.0, 40.0, 2.0 # %

# MET assignment limits
BAlimitWeathered, RPBlimitPB = 4.9, 45.0 # %
RPBlimitOX, SPBlimitOX, ZNPBmaxOX = 46.5, 8.5, 0.585 # %
CUlimitLO, CUlimitHI = 0.18, 0.32 # 0.15% Cu minimal effect and 0.25% Cu strong effect, limits are 0.25 +/-0.07
CUlimitSlp, CUlimitInt = 1/(CUlimitHI-CUlimitLO), 1+CUlimitLO/(CUlimitHI-CUlimitLO)

# Concentrate Recovery Calculation Limits
ZNadjPBmin, PBadjPBmin = 0.1, 0.1 #

# Concentrate Recovery Limits
recLimitFE, recLimitZN, recLimitBA = 7, 7, 23 # %
ZnRecMin, ZnRecMax = 30, 93 # %
PbRecMin, PbRecMax = 15, 84 # %
AgRecZnMax, AgRecPbMax = 71, 87 # %
PbRecPbOxMax, AgRecPbOxMax = 87, 77 # %

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

# Grinding model parameters, 5 sections (TK2016 spreadsheet model)
# 1) Hardness estimate limits
Ab_min, Ab_max = 15.0, 300.0 # TK original model limits
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
highTPH = 672.0   # mt/hr, for SAG/BM limit flag and Oxide and Weathered limiting; 672tph (5.5 Mt/yr) is "high" as throughput with BBMWi of 3 kWh/mt is about 827 tph for non-VIP2 case
# 5) user input values for Throughput model
PRim = 2081.0 # kW, maximum, not net, power from IsaMill (nominally 835 kW in TK2016, however maximum is 3000 hp x 0.746 kW/hp x 93% motor eff = 2081 kW)
gc = 0 # Grinding Configuration: 0-Standard, 1-Pebble crusher, 2-Pre-crush
Solids_W_fr = 0.75 # fraction of solids by weight (default = 0.75)
# P80 values
P80fine, P80medium, P80coarse = 65.0, 65.0, 65.0 # um
# SAG parameters
# notes: 1) max power draw 1870 kW all SAGs; however as TK Jan 2017 memo used 1720 kW all SAGs
#        2) when fitting parameters: i) set P80 variable to mill measured for fitting period then ii) do BC% first, keep ML% const, do not increase Speed above 235 rpm
RPMsag1_2, RPMsag3 = 225, 225   # SAG Mill speed, RPM
BCsag1_2, BCsag3 = 0.140, 0.140 # SAG Ball Charge "ball filling", fraction
MLsag1_2, MLsag3 = 0.254, 0.254 # SAG Mill Load "total filling", fraction
# SAG Critical Speed (fractional) from RPM
CSsag_const = pow(2*sag_radius,0.5)/(42.3*18.16)
CSsag1_2, CSsag3 = RPMsag1_2*CSsag_const, RPMsag3*CSsag_const
# IsaMill power
PRim = 2081.0 # kW, maximum, not net, power from IsaMill (nominally 835 kW in TK2016, however maximum is 3000 hp x 0.746 kW/hp x 93% motor eff = 2081 kW)
PFimVbm = 23.895*pow(PRim-PRim_nl,-0.377) # Power Factor, IsaMill vs Ball Mill
PRim_net = (PRim-PRim_nl)*PFimVbm*1.0753  # net IsaMill power (in Ball Mill power equivalent)

# PCA class boundaries
PCA1 = [(0.07739765,-0.065052144,1),(0,-0.44449356,1),(0.7596754,-1.9022361,1),(1.8326122,-1.3898741,1),(0.77248174,-0.5780578,1),(0.07739765,-0.065052144,1)]
PCA2 = [(-0.32426587,-2.3706815,1),(0.7596754,-1.9022361,1),(0,-0.44449356,1),(-0.17570537,-1.3971936,1),(-0.32426587,-2.3706815,1)]
PCA3 = [(1.3209039,0.57174075,1),(3.224679,-0.44566396,1),(1.8326122,-1.3898741,1),(0.77248174,-0.5780578,1),(1.3209039,0.57174075,1)]
PCA4 = [(-0.73650986,-1.245879,1),(-0.17570537,-1.3971936,1),(-0.32426587,-2.3706815,1),(-0.6433958,-2.5317097,1),(-0.9405167,-2.3194454,1),(-1.1420099,-2.0472643,1),(-0.73650986,-1.245879,1)]
PCA5 = [(-0.17570537,-1.3971936,1),(0,-0.44449356,1),(-0.43072304,-0.31878603,1),(-0.6500919,-1.0023206,1),(-0.73650986,-1.245879,1),(-0.17570537,-1.3971936,1)]
PCA6 = [(0,-0.44449356,1),(0.07739765,-0.065052144,1),(0.33600292,1.0987418,1),(0,1.2890476,1),(-0.29675466,1.2451309,1),(-0.87999207,0.1545316,1),(-0.5769689,-0.16165164,1),(-0.43072304,-0.31878603,1),(0,-0.44449356,1)]
PCA7 = [(-0.87999207,0.1545316,1),(-1.7136983,-1.1987387,1),(-1.4677393,-1.5680045,1),(-0.5769689,-0.16165164,1),(-0.87999207,0.1545316,1)]
PCA8 = [(-1.4677393,-1.5680045,1),(-1.1420099,-2.0472643,1),(-0.73650986,-1.245879,1),(-0.6500919,-1.0023206,1),(-0.43072304,-0.31878603,1),(-0.5769689,-0.16165164,1),(-1.4677393,-1.5680045,1)]
PCA9 = [(1.3209039,0.57174075,1),(0.33600292,1.0987418,1),(0.07739765,-0.065052144,1),(0,-0.44449356,1),(0.07739765,-0.065052144,1),(0.77248174,-0.5780578,1),(1.3209039,0.57174075,1)]
PCA10 = [(-0.29675466,1.2451309,1),(-1.6172923,0.9157553,1),(-1.7136983,-1.1987387,1),(-0.87999207,0.1545316,1),(-0.29675466,1.2451309,1)]
PCA11 = [(-1.1420099,-2.0472643,1),(-1.474234,-2.619543,1),(-0.946019,-3.6442673,1),(-0.4783286,-3.702823,1),(-0.32426587,-2.3706815,1),(-0.6433958,-2.5317097,1),(-0.9405167,-2.3194454,1),(-1.1420099,-2.0472643,1)]

# Throughput and recovery efficency
## TPH_eff, ZnRec_eff = 1.04, 1.01 # base case, "PTV150" +4% and +1.0% increase
TPH_eff, ZnRec_eff = 1.09, 1.022 # Race 23 "better" case, "PTV500" +9% and +2.2% total increase (note: not incremental) This is now the Base Case for LOM 2023, updated Jan 19, 2022
##TPH_eff, ZnRec_eff = 1.17, 1.042 # Race 23, better Case, Scenario 6 "crank it up" for LOM 2023, Updated March 9, 2022

#==============================================================================
# Panel 1
#==============================================================================

file15 = StringRTV(name="file15")

NGPperiod = IntegerRTV(name="perFlag", value=0)
PERLT_FUNCTIONS = ["no, apply to all blocks", "yes, apply only to unassigned periods"]
perFunction = IntegerRTV(name="perFunction")

class DefineModelFile(GPanel):

   def makewidgets(self):
      self.makeFilePickers()
      self.makePeriodFlag()

   def makeFilePickers(self):
      grp = GGroup(self, text="Choose model file")
      grp.pack(anchor=NW, pady=2, padx=2, ipadx = 2, ipady=2)
      item15 = cmpsys.getpcf().filelistbytype(15)
      cbs = GComboBox(grp.interior(), items=item15, rtv=file15)
      lbls = GLabel(grp.interior(), text="Name of 3D block model:")
      gtools.stdwidgetcolumns([lbls], [cbs])
      self.remember([cbs])

   def makePeriodFlag(self):
      grp = GGroup(self, text="Period filter?")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      rbut = GRadio(grp.interior(), items=PERLT_FUNCTIONS, rtv=perFunction)
      rbut.pack(anchor=NW, padx=4, pady=4)
      self.remember([rbut])

#==============================================================================
# Folder Layout
#==============================================================================

PANEL1 = "Model File Information"
PROC_FOLDERS = GFolder("Model Operations",[GItem(PANEL1, DefineModelFile)])

#==============================================================================
# Execution Functions
#==============================================================================

def ExecuteModelCalc(projectpath):
   projinf = cmpsys.getproject()
   pcffile = projinf.get(grail.compass.projectinfo.PCFPATH_TAG)
   projdir = fileutils.getdir(projectpath)
   pcfpath = projdir+'\\'+pcffile
   PythonLog = projdir+"\RunLog-Python_scripts.txt" # will create an empty file if none present in model folder
   PyLogFile = open(PythonLog,"a")
   DT = datetime.today()
   msgText = "\n"+DT.strftime("%d-%b-%Y  %H:%M\n")+"User: "+getpass.getuser()+"\n"+"Script: "+PROC_TITLE
   PyLogFile.write(msgText)

   #  replacement for col, row, level spinners
   pcf = cmpsys.getpcf()
   blockVolume = pcf.dx()*pcf.dy()*pcf.dz()
   minColumn, minRow, minLevel = 1, 1, 1
   maxColumn, maxRow, maxLevel = pcf.nx(), pcf.ny(), pcf.nz()
##   minColumn, minRow, minLevel = 1, 1, 25
##   maxColumn, maxRow, maxLevel = pcf.nx(), pcf.ny(), 25
##   minColumn, minRow, minLevel = 84, 59, 25
##   maxColumn, maxRow, maxLevel = 84, 59, 25

   # check if path to a Qanaiyaq model
   isQanaiyaq = "QAN" in pcfpath or "qan" in pcfpath or "Qan" in pcfpath
   if isQanaiyaq:
      msgText = "\n  Qanaiyaq model "+file15.get()+" in "+projdir+"\n"
      print msgText
      PyLogFile.write(msgText)
      msgText = "  Sulfide, Oxide, and Weathered metallurgy\n"
      print msgText
      PyLogFile.write(msgText)
   else:
      msgText = "\n  Aqqaluk model "+file15.get()+" in "+projdir+"\n"
      print msgText
      PyLogFile.write(msgText)
      msgText = "  Sulfide metallurgy\n"
      print msgText
      PyLogFile.write(msgText)

#####################################################
###  DEBUGGING / ANALYSIS code for Throughput model
##
##   sagData = projdir+"\sagData.csv" # will create an empty file if none present in model folder
##   sagDataFile = open(sagData,"w")
##   sagText = "Level,Row,Column,PRsag1_2,PRsag3,PRbm+im,SG,Ab,BBMWi,F80,T80,P80,P1in,SEsag,SEbm,TPHsag,TPHbm,MPTsag,MPTbm\n"
##   sagDataFile.write(sagText)
#####################################################

   # determine if calculations filtered by period
   period_filter = perFunction.get()>0
   if period_filter:
      msgText = "  Apply only to unassigned periods\n"
   else:
      msgText = "  Apply to all blocks\n"
   print msgText
   PyLogFile.write(msgText)

   # assume run fails unless last line overwritten
   PyLogFile.write("Failed!\n")

   for b in xrange(minLevel,maxLevel+1):
      print "  Opening and updating Bench: %2d" % (b)
      try:
         m = model.Model(pcfpath, file15.get(), b, b, minRow, maxRow, minColumn, maxColumn, itemlist)
      except model.ModelError, e:
         msgText = "Model Access Error: "+str(e)+"\n"
         print msgText
         PyLogFile.write(msgText)
         msgText = "Failed\n"
         print msgText
         PyLogFile.write(msgText)
      else:
         if m != None:
            slab = m.slab()
            cols, rows = slab.maxcolumn(), slab.maxrow()
            l = 0
            # traverse the slab, get values, calculate, and set the new values
            for r in xrange(rows):
               for c in xrange(cols):
                  if period_filter:
                     PERLT = slab["PERLT", l, r, c]
                     run_calcs = PERLT < 1
                  else:
                     run_calcs = True
                  if run_calcs:
                     # read model values required for all runs through script
                     workGEOL = slab["GEOL", l, r, c]
                     isAir = workGEOL == Air
                     workGEOL1 = slab["GEOL1", l, r, c]
                     workGEOSM = slab["GEOSM", l, r, c]
                     DEP = int(slab["DEP", l, r, c])
                     d = DEP - 1 # array indices: Main = 0, Aqqaluk = 1, Paalaaq = 2, Qanaiyaq = 3
                     workSTZN = slab["STZN", l, r, c]
                     STZN_defined = model.isdefined(workSTZN)>0
                     workSTPB = slab["STPB", l, r, c]
                     STPB_defined = model.isdefined(workSTPB)>0
                     STZNPB_defined = STZN_defined and STPB_defined
                     workSTSPB = slab["STSPB", l, r, c]
                     STSPB_defined = model.isdefined(workSTSPB)>0
                     if not STSPB_defined:  # assign STSPB grade
                        workPB = slab["PB", l, r, c]
                        workSPB = slab["SPB", l, r, c]
                        if model.isdefined(workPB)<1 or model.isdefined(workSPB)<1: # i.e. PB or SPB is not defined
                           ddh_RPB_defined = False
                           if (not isQanaiyaq and workGEOSM in Weathered[d]) or (isQanaiyaq and (workGEOL1 in Weathered[d] or workGEOL1 in Oxide[d] or workGEOSM in Oxide[d])):
                              workSTSPB = round(workSTPB * pctRPBweathered[d],2)
                           else:
                              workSTSPB = round(workSTPB * pctRPBnonweathered[d],2)
                        elif workPB == 0 or workSPB == 0: # PB and SPB are defined, but one or other is 0
                           ddh_RPB_defined = False
                           workSTSPB = 0.0
                        else: # use LT assay for RPB ratio
                           ddh_RPB_defined = True
                           ddh_RPB = min(workSPB,workPB)/workPB
                           workSTSPB = round(workSTPB * ddh_RPB,2)
                     workSTFE = slab["STFE", l, r, c]
                     STFE_defined = model.isdefined(workSTFE)>0
                     STZNPBFE_defined = STZNPB_defined and STFE_defined
                     if not STFE_defined:
                        workSTFE = 0.0
                     workSTBA = slab["STBA", l, r, c]
                     if model.isdefined(workSTBA)<1:
                        workSTBA = 0.0
                     workAG = slab["AG", l, r, c]
                     if model.isdefined(workAG)<1:
                        workAG = 0.0
                        AGM = model.UNDEFINED
                     else:
                        AGM = round(workAG*34.28572,1)
                     workTOC = slab["TOC", l, r, c]
                     if model.isdefined(workTOC)<1:
                        workTOC = 0.0
                     workS = slab["S", l, r, c]
                     if model.isdefined(workS)<1:
                        workS = 0.0
                     workSIO2 = slab["SIO2", l, r, c]
                     SIO2_defined = model.isdefined(workSIO2)>0
                     workCU = slab["CU", l, r, c]
                     CU_defined = model.isdefined(workCU)>0
                     workT1 = slab["T1", l, r, c]
                     workT2 = slab["T2", l, r, c]
                     workT6 = slab["T6", l, r, c]
                     TexturesNotDefined = model.isdefined(workT1)<1 or model.isdefined(workT2)<1 or model.isdefined(workT6)<1
                     ODENM = slab["ODENM", l, r, c]
                     SG = slab["SG", l, r, c]
                     NSG = slab["NSG", l, r, c]
                     KeyCreek = slab["KCFLG", l, r, c] == 1  # True if Key Creek formation
                     SHPCT = slab["SHPCT", l, r, c]
                     isAllShale = SHPCT >= 100                      # True if 100% shale
                     isAllSulfides = SHPCT <= 0                     # True if 100% sulfide
                     isMixed = not isAllShale and not isAllSulfides # True if 1% to 99% mixed shale-sulfide
                     hasSulfides = isAllSulfides or isMixed         # True if 1% to 100% sulfides

                     # grade and ratio calculations
                     if STSPB_defined and STPB_defined and workSTPB > 0:
                        RPB = int(round(workSTSPB/workSTPB * 100.0,0)) # RPB written to model based only on actual STSPB, not estimated
                        ZNPB = round(workSTZN/workSTPB,2) #### STPB is the total sulphide in the rock, STSPB: Non sulphide content in
                        RPB_defined = True
                        ZNPB_defined = True
                     else:
                        RPB = model.UNDEFINED
                        ZNPB = model.UNDEFINED
                        RPB_defined = False
                        ZNPB_defined = False

                     if STZN_defined and STFE_defined and workSTFE > 0:
                        ZNFE = round(workSTZN/workSTFE,2)
                        ZNFE_defined = True
                     else:
                        ZNFE = model.UNDEFINED
                        ZNFE_defined = False
                     ##  RECPB = max(workSTPB - (0.875 * workSTSPB), 0.0)  # "recoverable lead" for historical interest, not saved in block model any more

                     # ORCT1 (uses GEOSM, i.e. mixed geology coding)
                     if isAir:
                        ORCT1 = model.UNDEFINED
                     elif isQanaiyaq:
                        if workGEOSM in Block_1_Q:
                           ORCT1 = 1
                        elif workGEOSM in Block_2_Q:
                           ORCT1 = 2
                        elif workGEOSM in Block_3_Q:
                           ORCT1 = 3
                        elif workGEOSM in Block_4_Q:
                           ORCT1 = 4
                        elif workGEOSM in Block_5_Q:
                           ORCT1 = 5
                        else:
                           ORCT1 = 6 #undefined
                     else: # Main, Aqqaluk, or Paalaaq
                        if workGEOSM in Lower_Plate_A:
                           ORCT1 = 8
                        elif workGEOSM in Middle_Plate_A:
                           ORCT1 = 1
                        elif workGEOSM in Sublower_Plate_P:
                           ORCT1 = 6
                        else:
                           ORCT1 = 5

                     # ORCT2 (uses GEOSM, i.e. mixed geology coding)
                     if isAir:
                        ORCT2 = model.UNDEFINED
                     elif isAllShale: # classify 100% shale blocks first
                        if workGEOSM in Black_Shale[d]:
                           ORCT2 = 5
                        elif workGEOSM in Siksikpuk[d] or workGEOSM in Baritic_Siksikpuk[d]: # construction shales
                           ORCT2 = 6
                     elif isQanaiyaq and (workGEOSM in Oxide[d] or workGEOL1 in Oxide[d]):  # because this is set first Weathered below has no Oxide
                        ORCT2 = 7
                     elif (not isQanaiyaq and workGEOSM in Weathered[d]) or (isQanaiyaq and workGEOL1 in Weathered[d]):
                        ORCT2 = 2
                     elif workGEOSM in Exhalite[d]:
                        if workSTFE < FElimit and workSTBA < BAlimit:
                           ORCT2 = 1  # Exhalite
                        elif workSTBA >= BAlimit:
                           ORCT2 = 3  # Baritic
                        else: # workSTFE >= FElimit
                           ORCT2 = 4  # Iron-rich
                     elif workGEOSM in Vein[d]:
                        ORCT2 = 8
                     elif workGEOSM in Baritic[d]:
                        ORCT2 = 3
                     # assignment for shales
                     if isQanaiyaq:
                        if workGEOSM >= 201:
                           ORCT2 = workGEOSM - 190 # thus ORCT2 set to 11 to 13
                     elif workGEOSM >= 25: # assignment for non-Qanaiyaq codes
                        ORCT2 = workGEOSM - 15 # thus ORCT2 set to 10 to 18

                     # calculate Fe in Sphalerite lattice
                     if STZN_defined and workSTZN > 0:
                        FEinFeS = workSTZN*min(workSTFE/workSTZN,FEinZN)
                        FEinFeS2 = workSTFE - FEinFeS
                     else:
                        FEinFeS = 0.0
                        FEinFeS2 = workSTFE

                     # calculate Self Heating Capacity Risk Region and Blasting Agent Reactivity
                     if hasSulfides:
                        if STZNPBFE_defined:
                           Sph = workSTZN/0.6709 + FEinFeS/0.6352
                           Pyr = FEinFeS2/0.4655
                           Ang = workSTSPB/0.6832
                           Bar = workSTBA/0.5884

                           # Self Heating Capacity Risk Region (Nessetech 2016), compute A/B then RR: 1=safe, 2=will not heat >100C, 3= do not expose to high heat, 4=monitor, 5=preventative action required; assign 0 for non-sulphide and 6 for undefined sulphide
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
                           Sph_Pyr_defined = Pyr > 0
                           if Sph_Pyr_defined:
                              Sph_Pyr = Sph/Pyr
                           if RPB_defined and Sph_Pyr_defined and (RPB >= 10 and RPB <= 95) and Sph_Pyr <= 1.42 and Pyr >= 6.2 and workS >= 0.12:
                              # eta AA basis
                              eta = min(max(101.2 - 22.6234*Pyr + 7.53677*Ang - 325.38*Sph_Pyr + 43.4091*B,-10.0),10.0)
                              RXNmax_AA = exp(eta)/(1 + exp(eta))
                              # eta XRF basis
                              eta = min(max(395.764 - 5.13326*NSG - 21.3756*Bar - 60.4365*Pyr - 9.35528*Sph + 138.797*B - 80.0252*min(SHCRR,5),-10.0),10.0)
                              RXNmax_XRF = exp(eta)/(1 + exp(eta))
                              if RXNmax_AA >= 0.5 or RXNmax_XRF >= 0.5:
                                 BRXNF = 1  # reaction possible with Urea in blends
                              else:
                                 BRXNF = 0  # reaction possible without Urea
                           else:
                              BRXNF = model.UNDEFINED  # no reaction, with or without Urea

                        else: # STZNPBFE not defined
                           SHCRR = 6
                           BRXNF = 1 # worst case assumed, i.e. reaction possible with Urea in blends
                     else: # all remaining, non-sulfide containing rock and all Air
                        # set Blasting Agent Reactivity
                        SHCRR = 0
                        BRXNF = model.UNDEFINED # no reaction, with or without Urea
                     # set BA Reaction Flag exception for Ikalukrok shale (due to pyrite inclusions)
                     if workGEOL in BA_shale_reactive[d] and BRXNF != 1: # check BRXNF for mixed shale blocks, tag incase sulfide portion does not exhibit high reactivity from above calculations
                        BRXNF = 0  # reaction possible without Urea

                     # Set waste segregation criteria WARDC => 0-Possibly Reactive, 1-Low Reactive, 2-Construction, 3-Cover. For 2-Construction these are "polygon" criteria, not "hole" criteria, as they are applied to model blocks.
                     # Note: undefined assays are set to 0's when read in from Block Model so grade criteria only apply for some GEOL codes.
                     if KeyCreek and isAllShale:
                        WARDC = 3
                     elif not isMixed and (workGEOSM in Siksikpuk[d] or workGEOSM in Baritic_Siksikpuk[d] or workGEOSM in Baritic[d] or workGEOSM in Exhalite[d]) and STZNPBFE_defined and workSTZN <= 0.5 and workSTPB <= 0.5 and workSTFE <= 2.5:
                        WARDC = 2
                     elif SHCRR >= 5: # "take preventative action" on chart, here called "Possibly Reactive"
                        WARDC = 0
                     else: # remainder is non/low reactive (including Air)
                        WARDC = 1

                     # ore host rock type specific metallurgy calculations
                     if hasSulfides and STZNPB_defined:
                        # ensure textures defined, else use defaults
                        if TexturesNotDefined:
                           if workGEOSM in Baritic[d]:
                              workT1 = T1_baritic[d]
                              workT2 = T2_baritic[d]
                              workT6 = T6_baritic[d]
                           elif workGEOSM in Vein[d]:
                              workT1 = T1_vein[d]
                              workT2 = T2_vein[d]
                              workT6 = T6_vein[d]
                           elif ORCT2 == 2 or ORCT2 == 7:
                              workT1 = T1_weathered[d]
                              workT2 = T2_weathered[d]
                              workT6 = T6_weathered[d]
                           else: # exhalite as default
                              workT1 = T1_exhalite[d]
                              workT2 = T2_exhalite[d]
                              workT6 = T6_exhalite[d]

                        # assign MET codes
                        if DEP <= 2: # Main or Aqqaluk (these have been simplified from original 5 as only Weathered was extraordinary)
                           if RPB >= RPBlimit and workSTSPB >= SPBlimit: # all Weathered by RPB + sPb criteria (same definition used for Qanaiyaq MET)
                              MET = 2 # Weathered
                           else:
                              MET = 1 # Regular
                        elif DEP <= 3: # Paalaaq
                           if workGEOSM in Exhalite[d]:
                              if workSTBA >= BAlimit:
                                 MET = 9
                              else:
                                 MET = 7
                           elif workGEOSM in Vein[d]:
                              MET = 8
                           else: # workGEOSM in Baritic[d]:
                              MET = 9
                        else: # DEP == 4, Qanaiyaq
                           MET1_2RecoveryDeduct = False
                           if not CU_defined or not RPB_defined: # waste
                              MET = 0
                           elif ORCT2 == 7 or (RPB >= RPBlimitOX and workSTSPB >= SPBlimitOX and ZNPB_defined and ZNPB < ZNPBmaxOX): # possible High Lead-Silver Oxide (lead concentrate)
                              MET = 3
                           else:
                              if RPB < RPBlimit or (RPB >= RPBlimit and workSTSPB < SPBlimit): # Regular (zinc & lead)
                                 MET = 1
                              elif RPB < RPBlimitPB: # i.e. between RPBlimit and RPBlimitPB; note that all sPb's will be > SPBlimit
                                 if workCU < CUlimitHI: # Regular (zinc & lead)
                                    MET = 1
                                    MET1_2RecoveryDeduct = workCU > CUlimitLO # flag True in linear reduction region
                                 else:
                                    MET = 4 # remaining is Weathered High Copper (bulk concentrate)
                              else: # RPB >= RPBlimitPB; note that all sPb's will be > SPBlimit
                                 if workCU < CUlimitHI: # Weathered (zinc only)
                                    MET = 2
                                    MET1_2RecoveryDeduct = workCU > CUlimitLO # flag True in linear reduction region
                                 else:
                                    MET = 4 # remaining is Weathered High Copper (bulk concentrate)

                        # WXFG and QWXFG (Weathered flag for mill feed; metallurgical, not geological, based definition; weathered = 1, unweathered = 0)
                        QWXFG = int(isQanaiyaq and MET >= 2)  # Note: given the copper parameter in Qanaiyaq MET coding, Weathered in Qan has >= RPBlimitPB whereas Weathered in Aqq has >= RPBlimit
                        WXFG = max(int(not isQanaiyaq and MET == 2), QWXFG)

                        # set minima for grades near zero for Main and Aqqaluk deposit recovery, and all deposit AG recovery, calculations
                        ZN = max(workSTZN,ZNmin)
                        PB = max(workSTPB,PBmin)
                        if not RPB_defined or workSTSPB == 0 or RPB == 0: # in case sPb=0
                           if ddh_RPB_defined: # !!! removed the rounding to 2 decimal places in the SPB calcs below on May 22 as made SPB=0.00 with very low ddh_RPB ratios, i.e. round(PB * ddh_RPB,2) and did not seem to be required (?)
                              SPB = PB * ddh_RPB
                           else:
                              if (not isQanaiyaq and workGEOSM in Weathered[d]) or (isQanaiyaq and (workGEOL1 in Weathered[d] or workGEOSM in Oxide[d])):
                                 SPB = PB * pctRPBweathered[d]
                              else:
                                 SPB = PB * pctRPBnonweathered[d]
                        else:
                           SPB = PB * workSTSPB/workSTPB
                        BA = max(workSTBA,BAmin)
                        FE = max(workSTFE,FEmin)
                        FEinFeS_met = ZN*min(FE/ZN,FEinZN) # ZN always > 0 due to minima calculations, so do not need ZN=0 logic
                        FEinFeS2_met = FE - FEinFeS_met
                        NSGmet = 100.0 - (ZN/0.6709 + (PB-SPB)/0.8660 + SPB/0.6832 + FEinFeS2_met/0.4655 + FEinFeS_met/0.6352 + BA/0.5884 + workS + workTOC)
                        if NSGmet < NSGmin:  # recalc NSG and Ba for use in Universal Model
                           deltaNSG = NSGmin - NSGmet
                           BA = max((BA/0.5884 - deltaNSG)*0.5884,BAmin)
                           NSGmet = NSGmin

                        # Zinc, Lead, and Bulk concentrate grades and recoveries
                        if not isQanaiyaq:  # Main, Aqqaluk, Paalaaq
                           # set Oxide and Weathered metallurgy to zero as only in Qanaiyaq
                           PBROX, PBGOX = 0.0, 0.0
                           ZNRWX, ZNGWX, PBRWX, PBGWX = 0.0, 0.0, 0.0, 0.0

                           if DEP <= 2 or (DEP == 3 and MET == 9): # only for Main, Aqqaluk, and baritic Paalaaq
                          #  if DEP <= 3: # for Main, Aqqaluk, and Paalaaq
                              ZNGRD = 53.0
                              PBGRD = 54.5
                              RPBmet = SPB/PB * 100.0
                              sulPB = PB - SPB
                              ZNadjPB = max(11.0692 * exp(-0.0239*RPBmet) - 0.5748*sulPB, ZNadjPBmin)
                              PBadjPB = max(4.0118 * exp(-0.0766*RPBmet) + 0.5396*sulPB, PBadjPBmin)

                              # zinc concentrate
                              if FE <= recLimitFE and ZN <= recLimitZN and BA >= recLimitBA:  # use original ZNREC model as exponential model over-estimates recovery for low Zn, low Fe, high Ba blocks
                                 ZNREClab = 35.8735*pow(ZN,0.2504)*pow(PB,-0.1601)*pow(FE,-0.05875)*pow(NSGmet,0.09152)
                                 ZNREClab = min(max(ZNREClab,ZnRecMin),ZnRecMax)  # min now 30, was 40 in old URF
                              else:  # use revised, exponential model
                                 if MET == 2:  # limit high BA grades for milling criteria weathered Aqqaluk/Main, note that NSG is not recalculated and only MET=9 for Paalaaq here
                                    BA = min(BA,BAlimitWeathered)
                                 e1 = 0.0161 * BA + 0.2481
                                 e2 = -0.0024 * BA - 0.0888
                                 e3 = -0.0075 * BA + 0.0740
                                 e4 = -0.0018 * BA + 0.1491
                                 e5 = 0.0117 * BA + 0.0136
                                 e6 = -0.0160 * BA + 0.0029
                                 e7 = -0.0405 * BA + 0.1711
                                 ZNREClab = 17.469*pow(ZN,e1)*pow(PB,e2)*pow(FE,e3)*pow(NSGmet,e4)*pow(BA,e5)*pow(SPB,e6)*pow(ZNadjPB,e7)
                              Y = max(4.60517 - log(ZNREClab),0.0001)
                              if ORCT2 == 3: # Baritic ore type; May 2016 Baritic specific plant transfer function
                                 Z = ZNREClab + (10.7349/Y) * exp(-0.5*pow((log(Y)+0.42027)/0.58708,2))
                              else: # April 2003 plant transfer function
                                 Z = ZNREClab + (4.0746/Y) * exp(-0.5*pow((log(Y)+0.87774)/0.42255,2))
                              Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
                              ZNREC = min(max(Z,ZnRecMin),ZnRecMax)

                              # lead concentrate
                              if MET == 2: # no Pb conc produced for milling criteria weathered Aqqaluk/Main, note that only MET=9 for Paalaaq here
                                 PBREC = 0.0
                              else:
                                 e1 = 0.0762 * FE - 0.3363
                                 e2 = -0.3824 * FE + 3.6151
                                 e3 = 0.000 * FE - 0.1788
                                 e4 = 0.0410 * FE - 0.0603
                                 e5 = 0.0075 * FE - 0.0419
                                 e6 = 0.1602 * FE - 1.6041
                                 e7 = 0.2504 * FE - 2.4251
                                 PBREClab = round(9.24*pow(ZN,e1)*pow(PB,e2)*pow(FE,e3)*pow(NSGmet,e4)*pow(BA,e5)*pow(SPB,e6)*pow(PBadjPB,e7),2)
                                 PBREC = min(max(PBREClab,PbRecMin),PbRecMax)
 
 ###Not used per David Lin memo (to add date)
 ###removed DJM Jan 18, 2022
 ###not for use in official model
                           else: # DEP == 3, Paalaaq, MET = 7 or 8
                             if MET == 8: # Veined, ore Type B
                                ZNGRD = 53.0
                                PBGRD = 54.5
                                ZNREC = round(81.3*ZnRec_eff,1)
                                PBREC = 67.0
                             else: # MET = 7, Siliceous, ore Type A
                                ZNGRD = 53.0
                                PBGRD = 54.5
                                ZNREC = round(43.8*ZnRec_eff,1)
                                PBREC = 49.6
                        else: # Qanaiyaq (DEP == 4)
                           ZNGRD = 53.0
                           PBGRD = 54.5
                           PBGOX = 45.0
                           ZNGWX = 40.5
                           PBGWX = 7.5

                           # zinc concentrate (only sulphide) or bulk concentrate zinc (only High Cu)
                           # Regular (zinc & lead) or Weathered (zinc)
                           if MET == 1 or MET == 2:
                              if SIO2_defined:
                                 AGclip = max(min(workAG,6.912),1.158) # clip AG based on range of data used to develop model
                                 TOCclip = max(min(workTOC,0.65),0.10) # clip TOC based on range of data used to develop model
                                 ZZ = 13.78371 + 1.32534*workSTZN - 1.85221*workSTSPB + 0.66301*workSIO2 + 2.20423*AGclip - 13.85855*TOCclip + 0.21601*workT2
                                 if MET1_2RecoveryDeduct: # transition area where Cu% between LO and HI and RPB >= RPBlimit
                                    CUreduction = max(min(CUlimitInt - CUlimitSlp*workCU,1.0),0.0) # linear reduction to recovery for region between LO and HI limits
                                    Z = CUreduction*ZZ
                                 else:
                                    Z = ZZ # as CUreduction = 1.0
                                 Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
                                 ZNREC = min(max(Z,0),ZnRecMax)
                              else:
                                 ZNREC = 0.0
                           else: # no regular Zinc concentrate from 3-High Lead-Silver Oxide, 4-Weathered High Copper, or 0-Waste
                              ZNREC = 0.0
                           # Weathered High Copper
                           if MET == 4 or MET1_2RecoveryDeduct: # calculate for overlap region only (**OR** calculate for all weathered, i.e. RPB_defined and RPB >= RPBlimit and workSTSPB >= SPBlimit)
                              Z = 6.67*workSTZN-33.33 # assume linear relationship; test feed of 17% Zn gave 80% Rec and assume a feed of 5% Zn would give 0% Rec
                              Z = round(Z*ZnRec_eff,2)    # zinc flotation circuit efficency adjustment
                              ZNRWX = min(max(Z,0),ZnRecMax)
                           else:  # no potential for Bulk concentrate from 3-High Lead-Silver Oxide or 0-Waste
                              ZNRWX = 0.0

                           # lead concentrate (sulphide and oxide) or bulk concentrate lead (only High Cu)
                           # Regular (zinc & lead)
                           if MET == 1:
                              P = round(63.67652 - 11.3144*workSTSPB + 1.044188*workSTPB,2)  # without Cu assay as Cu not statistically significant in regression
                              PBREC = min(max(P,0),PbRecMax)
                           else: # no regular lead concentrate from 2-Weathered (zinc conc only), 3-High Lead-Silver Oxide, 4-Weathered High Copper, or 0-Waste
                              PBREC = 0.0
                           # High Lead-Silver Oxide
                           if MET == 3:
                              if workSTPB > 0:
                                 P = round(67.2*log(workSTPB) - 104.0,2)  # recovery modelled from data in D.Lin (File Note; Sept 12, 2017)
                                 PBROX = min(max(P,0),PbRecPbOxMax)
                              else:
                                 PBROX = 0.0
                           else: # no Oxide concentrate from 1-Regular (zinc & lead), 2-Weathered (zinc), 4-Weathered High Copper, or 0-Waste
                              PBROX = 0.0
                           # Weathered High Copper
                           if MET == 4 or MET1_2RecoveryDeduct: # calculate for overlap region only (**OR** calculate for all weathered, i.e. RPB_defined and RPB >= RPBlimit and workSTSPB >= SPBlimit)
                              if workSTPB > 0:
                                 ConcTns = workSTZN*ZNRWX/ZNGWX
                                 P = round(ConcTns*PBGWX/workSTPB,2)
                                 if P <= PbRecMax: # ideally this should balance with zinc metallurgy so should not need a max limit; however, the calculated value was found to go up to 100% so a limit check is required
                                    PBRWX = max(P,0)
                                 else: # if Pb recovery is clipped then new concentrate Pb grade must be computed at that recovery
                                    PBRWX = PbRecMax
                                    PBGWX = round(workSTPB*PBRWX/ConcTns,2)
                              else:
                                 PBRWX = 0.0
                           else: # no potential for Bulk concentrate from 3-High Lead-Silver Oxide or 0-Waste
                              PBRWX = 0.0

                        # silver grade (grams/tonne) in zinc, lead, and bulk concentrates; calculate recovery then convert to grade
                        # Regular, i.e. Main, Aqqaluk, Paalaaq, or Qanaiyaq (sulphide ore MET codes)
                        if DEP <= 3 or (DEP == 4 and (MET == 1 or MET == 2)):
                           # Ag recovery to Oxide Pb concentrate
                           AGGOX = 0.0
                           # Ag recovery to zinc concentrate
                           if workTOC > 0 and ZNREC > 0:  # and FE > 0 and NSGmet > 0
                              A = 0.71200*exp(-7.416)*pow(FE,0.1988)*pow(workTOC,-0.1760)*pow(NSGmet,-0.4080)*pow(ZNREC,2.659) + 19.05360
                              AgRecZn = min(max(A,0),AgRecZnMax)
                           else:
                              AgRecZn = 0.0
                           # Ag recovery to lead concentrate
                           if workAG > 0 and PBREC > 0 and not(DEP == 4 and MET == 2): # and PB > 0 and SPB > 0 and not 2-Weathered (zinc)
                              A = 0.50950*exp(-4.665)*pow(PB,1.459)*pow(SPB,-0.5752)*pow(workAG,-1.040)*pow(PBREC,1.517) + 14.41932
                              AgRecPb = min(max(A,0),AgRecPbMax)
                           else:
                              AgRecPb = 0.0
                           # cap Ag recoveries based on total recovery
                           AgRecTotal = AgRecZn + AgRecPb
                           if AgRecTotal > AgRecPbMax:
                              AgRecAdjust = AgRecPbMax/AgRecTotal
                              AgRecZn = AgRecZn*AgRecAdjust
                              AgRecPb = AgRecPb*AgRecAdjust
                           # convert Ag recoveries to Ag grades
                           if AgRecZn > 0 and workSTZN > 0 and ZNREC > 0:
                              AGGZN = round(AGM*AgRecZn/(workSTZN*ZNREC/ZNGRD),1)
                           else:
                              AGGZN = 0.0
                           if AgRecPb > 0 and workSTPB > 0 and PBREC > 0:
                              AGGPB = round(AGM*AgRecPb/(workSTPB*PBREC/PBGRD),1)
                           else:
                              AGGPB = 0.0
                        else: # Qanaiyaq 3-High Lead-Silver Oxide or 4-Weathered High Copper
                           # Ag recovery to zinc and lead concentrates
                           AGGZN = 0.0
                           AGGPB = 0.0
                           # Ag recovery to High Lead-Silver Oxide (Oxide Pb concentrate). NOTE: No overlap with any other MET, so inside this loop.
                           if MET == 3 and PBROX > 0 and AGM > 0:
                              A = 56.8*log(AGM) - 252.8  # from follow-up graph to Sept 12,'17 file note by D.Lin
                              AgRecPbOx = min(max(A,0),AgRecPbOxMax)
                              AGGOX = round(AGM*AgRecPbOx/(workSTPB*PBROX/PBGOX),1)
                           else:
                              AGGOX = 0.0
                        # Ag recovery to Weathered High Copper (Bulk concentrate). NOTE: This can come from MET 1, 2, or 4, so outside above loop.
                        if DEP == 4 and (MET == 4 or MET1_2RecoveryDeduct):
                           AGGWX = 381.0
                           if AGM > 0: # then can check for exception if recovery too high
                              ConcTns = workSTZN*ZNRWX/ZNGWX
                              AgRecWx = ConcTns*AGGWX/AGM
                              if AgRecWx > AgRecPbMax: # recovery too high so adjust grade
                                 AGGWX = round(AGM*AgRecPbMax/ConcTns,1)
                        else:
                           AGGWX = 0.0

                        # PCA parameter calculation
                        Gal = (workSTPB-workSTSPB)/0.8660
                        Sph = workSTZN/0.6709 + FEinFeS/0.6352
                        Pyr = FEinFeS2/0.4655
                        Bar = workSTBA/0.5884
                        U1YP = -0.004074671*Bar + 0.012634782*NSG - 0.025242613*Sph - 0.107611865*Gal - 0.015048441*Pyr - 0.00473548*10*workTOC
                        U2XP = 0.03159656*Bar - 0.000326032*NSG - 0.002455592*Sph - 0.014168624*Gal - 0.019183818*Pyr - 0.034004886*10*workTOC
                        U = (U2XP,U1YP,1)


                        # assign PCA class and calculate work index parameters, only Ab fully implemented as Class Based gives too low a BBMWi value (i.e. soft)
                        universal_Ab = True
                        universal_BBMWi = True
                        if point_inside_pointlist2d(U,PCA3)==1: # Baritic
                           ACLS = 3
                           P80 = P80coarse
                           if ZNFE_defined:
                              Ab = round(15.18*Gal + 2.054*Bar - 226.1*workTOC - 3.133*ZNFE,1)
                           else:
                              Ab = Ab_min
                           universal_Ab = False
                           BBMWi = round(14.23 - 0.144*workT2 - 0.0619*workT6 - 0.227*Sph,2)
                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA6)==1: # Siliceous
                           ACLS = 6
                           P80 = P80fine
                           Ab = round(71.33 - 0.223*workT6 - 1.049*Pyr + 1.141*Bar,1)
                           universal_Ab = False
##                           BBMWi = round(19.24 + 0.0997*workT6 - 2.886*Gal - 3.219*Bar,2)
##                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA4)==1: # Sphalerite
                           ACLS = 4
                           P80 = P80fine
                           Ab = round(27.45 + 0.556*workT2 + 0.638*Sph + 1.179*Bar,1)
                           universal_Ab = False
##                           BBMWi = round(8.596 + 0.0105*workT2 + 0.0422*NSG + 0.0302*Sph,2)
##                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA7)==1: # Sil-Pyr
                           ACLS = 7
                           P80 = P80fine
                           Ab = round(43.18 + 0.154*workT2 + 0.368*Sph + 3.905*Bar - 6.462*workTOC,1)
                           universal_Ab = False
##                           BBMWi = round(0.0236*workT2 + 0.275*NSG + 0.0783*Pyr - 9.717*Bar,2)
##                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA8)==1: # Pyr-Sph
                           ACLS = 8
                           P80 = P80fine
                           Ab = round(391.8 - 0.133*workT6 - 1.720*NSG - 74.554*SG,1)
                           universal_Ab = False
##                           BBMWi = round(-107.28 + 1.243*NSG + 1.394*Sph + 0.896*Gal + 1.088*Pyr,2)
##                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA5)==1: # Sil-Sph
                           ACLS = 5
                           P80 = P80fine
                           if ZNFE_defined:
                              Ab = round(37.06 + 0.562*workT2 + 26.35*workTOC + 0.867*ZNFE,1)
                           else:
                              Ab = Ab_min
                           universal_Ab = False
##                           BBMWi = round(0.0777*workT2 + 0.0925*workT6 + 0.083*NSG,2)
##                           universal_BBMWi = False
                        elif point_inside_pointlist2d(U,PCA1)==1: # Barite Transition
                           ACLS = 1
                           P80 = P80medium
                        elif point_inside_pointlist2d(U,PCA2)==1: # Sphalerite Transition
                           ACLS = 2
                           P80 = P80fine
                        elif point_inside_pointlist2d(U,PCA9)==1: # Sil-Barite Transition
                           ACLS = 9
                           P80 = P80medium
                        elif point_inside_pointlist2d(U,PCA10)==1: # High TOC Universal
                           ACLS = 10
                           P80 = P80fine
                        elif point_inside_pointlist2d(U,PCA11)==1: # High Galena Universal
                           ACLS = 11
                           P80 = P80fine
                        else: # not defined in any polygons
                           ACLS = 0
                           P80 = P80fine

                        # use Universal model for undefined classes or if Ab or BBMWi are out of limit with Class-based equation
                        # Ab
                        if universal_Ab or Ab < Ab_min or Ab > Ab_max:
                           if ZNFE_defined:
                              Ab = round(38.60 + 0.160*workT2 + 0.469*Sph + 1.295*Bar - 0.647*ZNFE,1)
                              Ab = min(max(Ab,Ab_min),Ab_max) # ensure limited whether from Class or Universal basis
                           else:
                              Ab = Ab_min
                        if QWXFG == 1: # exception for weathered Qanaiyaq as poor quality rock
                           Ab = min(max(150.0, Ab), Ab_max) # for friable material
                        # BBMWi
                        BBMWi_min = 66.748*pow(Ab,-0.445)
                        if isQanaiyaq: # Qanaiyaq; has custom BBMWi formula
                           BBMWi = round(0.49216*workSTZN + 0.2699*NSG - 0.10428*workT1,2)
                        else: # Main, Aqqaluk, Paalaaq
                           if universal_BBMWi or BBMWi < BBMWi_min or BBMWi > BBMWi_max: # use Universal form
                              BBMWi = round(5.772 + 0.0256*workT2 + 0.105*NSG + 4.95*workTOC,2)
                        BBMWi = min(max(BBMWi,BBMWi_min),BBMWi_max) # ensure limited whether from Class or Universal basis

                        # calculate specific energy and throughput
                        #============================
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
###################################################
###  DEBUGGING code for Throughput model
##
##                           print "SGslurry:%6.3f  VOLcharge:%7.3f  t_const:%6.3f  t:%6.3f  s:%7.4f  ALtemp1:%7.4f  ALtemp2:%7.4f  ALtemp3:%7.4f  AL_fract:%7.4f" % (SGslurry,VOLcharge,t_const,t,s,ALtemp1,ALtemp2,ALtemp3,AL_fract)
##                           print "z:%7.4f  KEA:%9.4f  PRnet:%7.1f  PRnl:%6.1f  PRgross:%7.1f" % (z,kinetic_energy_allowance,PRnet,PRnl,PRgross)
##                           print "row:%3d  col:%3d  bench:%3d\n" % ((r+minRow),(c+minColumn),minLevel)
###################################################
                           return PRgross;
                        # end of power calculation function
                        #==================================
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
##                        # calculate potential P80 if SAG mill limited and BM power not reduced (not used)
##                        SEbm_prod = (PRbm + PRim_net)/TPH
##                        P80_prod = pow(SEbm_prod/(10*BBMWi) + pow(Kbm[gc]*T80,-0.5),-2)
                        # grinding circuit efficency adjustment
                        if QWXFG: # i.e. isQanaiyaq and weathered, then limit to highTPH
                           TPH = min(TPH*TPH_eff,highTPH)
                        else:
                           TPH = TPH*TPH_eff
                        if TPH < highTPH: # set SAG/BM flag for "normal" throughputs
                           SAGFG = (TPHsag <= TPHbm) # if SAG limited then True (1) else if BM limited then False (0)
                        else: # do not define when throughput is "high"
                           SAGFG = model.UNDEFINED
###################################################
###  DEBUGGING / ANALYSIS code for Throughput model
##
##                     # explicitly convert SAGFG to S, B, or - for debugging text printout
##                     if SAGFG == 1:
##                        SGBM = 'S'
##                     elif SAGFG == 0:
##                        SGBM = 'B'
##                     else:
##                        SGBM = '-'
##
####                     print "SG:%5.2f  Ab:%7.2f  BBMWi:%6.2f  P1in:%5.1f  F80:%5.1f  T80:%4.0f  P80in:%3.0f  PRsag1_2:%5.0f  PRsag3:%5.0f  PRpcr:%4.0f  PRbm+im:%5.0f  TPHsag:%5.0f  TPHbm:%5.0f  Limit: %s\n" % (SG,Ab,BBMWi,P1in,F80,T80,P80,PRsag1_2,PRsag3,PRpcr_net,PRbm+PRim_net,TPHsag,TPHbm,SGBM)
##                     # or
##                        print "CS:%4.3f  BC:%4.3f  ML:%4.3f  SEsag:%6.2f  SEbm:%6.2f" % (CS,BC,ML,SEsag,SEbm)
##                        print "PRsag1_2:%5.0f  PRsag3:%5.0f  SG:%5.2f  Ab:%7.2f  DWI:%5.2f  F80:%5.1f  P1in:%5.1f" % (PRsag1_2,PRsag3,SG,Ab,DWI,F80,P1in)
##                        print "DWIAB:%5.2f  BBMWi:%6.2f  T80:%4.0f  P80in:%3.0f  TPH:%4.0f  row:%3d  col:%3d  bench:%3d\n" % (DWIAB,BBMWi,T80,P80,TPH,(r+minRow),(c+minColumn),minLevel)
##                     # or
##                     FLAG1 = slab["FLAG1", l, r, c]
##                     if model.isdefined(workT1) and FLAG1: # textures are defined
##                        sagText = "%2d,%3d,%3d,%4.0f,%4.0f,%4.0f,%4.2f,%3.0f,%4.1f,%5.1f,%5.1f,%4.1f,%4.1f,%5.2f,%5.2f,%4.0f,%4.0f,%8.6f,%8.6f\n" % (b,r+minRow,c+minColumn,PRsag1_2,PRsag3,PRbm+PRim_net,SG,Ab,BBMWi,F80,T80,P80,P1in,SEsag,SEbm,TPHsag,TPHbm,60.0/TPHsag,60.0/TPHbm)
##                        sagDataFile.write(sagText)
##                       # Level  Row  Column  PRsag1_2  PRsag3  PRbm+im   SG   Ab  BBMWi   F80   T80  P80  P1in  SEsag  SEbm  TPHsag  TPHbm   MPTsag    MPTbm
##                       #  37   180    180     4500     2300     4800   3.47  88   13.5  90.3  60.3  60.3  30.0  10.67  10.67  452     600  0.010101  0.010101
###################################################
                     else: # does not contain sulfides (thus can be Air) or STZN or STPB assays not defined
                        MET = 0
                        ACLS = 0
                        WXFG, QWXFG = 0, 0  # no grades so no metallurgical weathering estimation for these blocks
                        ZNGRD, ZNREC, AGGZN = 53.0, 0.0, 0.0 # Zn conc
                        PBGRD, PBREC, AGGPB = 54.5, 0.0, 0.0 # Pb conc
                        PBROX, AGGOX = 0.0, 0.0              # Pb-Ag oxide conc
                        ZNRWX, PBRWX, AGGWX = 0.0, 0.0, 0.0  # Zn-Cu weathered conc
                        # deposit specific defaults
                        if isQanaiyaq:
                           PBGOX = 45.6             # Pb-Ag oxide conc
                           ZNGWX, PBGWX = 40.5, 7.5 # Zn-Cu weathered conc
                           # host geology specific defaults (SEsag, SEbm, and TPH calculated using TK2016 model)
                           if workGEOSM in Black_Shale[d]:
                              # TF = Qan_Black_Shale_TF for computing grinding parameters
                              Ab = 42.8 # Ab & BBWWi from AQQ testing Black Shale as no QAN specific samples
                              BBMWi = 20.90
                              P80 = 60.0 # "P80coarse"
                              SEsag = 9.50
                              SEbm = 15.89
                              TPH = 439.3*TPH_eff # grinding circuit efficency adjustment
                              SAGFG = 0 # if SAG limited then True (1)
                         ##elif workGEOSM in Baritic_Siksikpuk[d]:  *** Commented out as Baritic Siksikpuk not separated from Siksikpuk in most recent Qanaiyaq model QAN2016; however, retained should Baritic Siksikpuk reappear
                         ##   # TF = Qan_Baritic_Siksikpuk_Shale_TF for computing grinding parameters
                         ##   Ab = 195.7 # Ab & BBWWi from AQQ testing Baritic Siksikpuk Shale as no QAN specific samples
                         ##   BBMWi = 9.09
                         ##   P80 = 60.0 # "P80coarse"
                         ##   SEsag = 5.62
                         ##   SEbm = 6.69
                         ##   TPH = 896.4*TPH_eff # grinding circuit efficency adjustment
                         ##   SAGFG = model.UNDEFINED # would be 1, but TPH is > 672 (highTPH) so undefined; if SAG limited then True (1)
                           elif workGEOSM > Air: # i.e. not air
                              # TF = Qan_Siksikpuk_Shale_TF for computing grinding parameters
                              Ab = 49.4 # Ab & BBWWi from AQQ testing Siksikpuk Shale as no QAN specific samples
                              BBMWi = 18.86
                              P80 = 60.0 # "P80coarse"
                              SEsag = 9.03
                              SEbm = 14.0
                              TPH = 498.8*TPH_eff # grinding circuit efficency adjustment
                              SAGFG = 0 # if SAG limited then True (1)
                        else: # Main, Aqqaluk, Paalaaq
                           PBGOX = 0.0             # Pb-Ag oxide conc
                           ZNGWX, PBGWX = 0.0, 0.0 # Zn-Cu weathered conc
                           # host geology specific defaults (SEsag, SEbm, and TPH calculated using TK2016 model)
                           if workGEOSM in Black_Shale[d]:
                              # TF = Black_Shale_TF for computing grinding parameters
                              Ab = 42.8
                              BBMWi = 20.90
                              P80 = 60.0 # "P80coarse"
                              SEsag = 11.56
                              SEbm = 15.88
                              TPH = 413.9*TPH_eff # grinding circuit efficency adjustment # 393.6
                              SAGFG = 1 # if SAG limited then True (1)
                           elif workGEOSM in Baritic_Siksikpuk[d]:
                              # TF = Baritic_Siksikpuk_Shale_TF for computing grinding parameters
                              Ab = 195.7
                              BBMWi = 9.09
                              P80 = 60.0 # "P80coarse"
                              SEsag = 5.60
                              SEbm = 6.78
                              TPH = 958.9*TPH_eff # grinding circuit efficency adjustment # 911.3
                              SAGFG = model.UNDEFINED # would be 1, but TPH is > 672 (highTPH) so undefined; if SAG limited then True (1)
                           elif workGEOSM > Air: # i.e. not air
                              # TF = Siksikpuk_Shale_TF for computing grinding parameters
                              Ab = 49.4
                              BBMWi = 18.86
                              P80 = 60.0 # "P80coarse"
                              SEsag = 10.32
                              SEbm = 14.0
                              TPH = 468.5*TPH_eff # grinding circuit efficency adjustment # 445.4
                              SAGFG = 1 # if SAG limited then True (1)

                     # calculate throughput and grinding hours
                     if isAir: # no geology as is in air
                        Ab = model.UNDEFINED
                        BBMWi = model.UNDEFINED
                        P80 = model.UNDEFINED
                        SEsag = model.UNDEFINED
                        SEbm = model.UNDEFINED
                        SAGFG = model.UNDEFINED
                        MPT = 0.0
                        GNDHR = 0.0
                     else: # geology defined
                        TonnesPerBlock = blockVolume*ODENM  # NOTE this is not adjusted by topo, will be taken care of by partials file
                        MPT = round(60.0/TPH,6)
                        GNDHR = round(TonnesPerBlock*MPT/60.0,2)

                     # write values to model
                     slab["AGM", l, r, c] = AGM
                     slab["ZNFE", l, r, c] = ZNFE
                     slab["ZNPB", l, r, c] = ZNPB
                     slab["RPB", l, r, c] = RPB
                     slab["ORCT1", l, r, c] = ORCT1
                     slab["ORCT2", l, r, c] = ORCT2
                     slab["QWXFG", l, r, c] = QWXFG
                     slab["WXFG", l, r, c] = WXFG
                     slab["P80", l, r, c] = P80
                     slab["WARDC", l, r, c] = WARDC
                     slab["MET", l, r, c] = MET
                     slab["ACLS", l, r, c] = ACLS
                     slab["ZNGRD", l, r, c] = ZNGRD
                     slab["ZNREC", l, r, c] = ZNREC
                     slab["PBGRD", l, r, c] = PBGRD
                     slab["PBREC", l, r, c] = PBREC
                     slab["AGGZN", l, r, c] = AGGZN
                     slab["AGGPB", l, r, c] = AGGPB
                     slab["AGGOX", l, r, c] = AGGOX
                     slab["PBROX", l, r, c] = PBROX
                     slab["PBGOX", l, r, c] = PBGOX
                     slab["AGGWX", l, r, c] = AGGWX
                     slab["ZNGWX", l, r, c] = ZNGWX
                     slab["PBGWX", l, r, c] = PBGWX
                     slab["ZNRWX", l, r, c] = ZNRWX
                     slab["PBRWX", l, r, c] = PBRWX
                     slab["SHCRR", l, r, c] = SHCRR
                     slab["BRXNF", l, r, c] = BRXNF
                     slab["MPT", l, r, c] = MPT
                     slab["GNDHR", l, r, c] = GNDHR
                     slab["SESAG", l, r, c] = SEsag
                     slab["SEBM", l, r, c] = SEbm
                     slab["AB", l, r, c] = Ab
                     slab["BMWi", l, r, c] = BBMWi
                     slab["SAGFG", l, r, c] = SAGFG
            m.storeslab()
            m.free()
         print "  Done"
   # if executes completely, remove and rewrite last line
   PyLogFile.close
   PyLogFile = open(PythonLog,"r")
   fileContents = PyLogFile.readlines()
   fileContents = fileContents[:-1] # remove last line of file
   PyLogFile.close
   PyLogFile = open(PythonLog,"w")
   for item in fileContents: # rewrites file content from list
      PyLogFile.write("%s" % item)
   PyLogFile.write("Executed OK\n")
   PyLogFile.close
###################################################
###  DEBUGGING / ANALYSIS code for Throughput model
##   sagText = "\n"
##   sagDataFile.write(sagText)
##   sagDataFile.close
###################################################

#==============================================================================
# Procedure Entry Points
#==============================================================================

def gmain(message, data):
   # main entry point
   if message is messages.gRUN:
      cmpsys.runprocedure(sys.argv[0], PROC_TITLE, PROC_FOLDERS, PANEL1)
   elif message is messages.gPOST_RUN:
      # did the user ok the run?
      if cmpsys.isgo():
         ExecuteModelCalc(cmpsys.getproject().path())
   else:
      # let the default compass behaviour handle it
      return gsys.grailmain(message, data)

#=============================================================================

# from the command line...
if __name__ == "__main__":
   cmpsys.fromcommandline(sys.argv, gmain)
