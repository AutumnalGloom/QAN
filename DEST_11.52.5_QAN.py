#==============================================================================
# Program to assign Destination Code
#
# Uses FLAG2 for intermediate storage of MGO flag.
#==============================================================================

import sys
from Tkinter import *
import tkMessageBox
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

#==============================================================================
# Version Information
#==============================================================================

PROC_TITLE = "Destination Coding - ver 11.52.5_QAN - Feb 26, 2024"

# May 6, 2012 - v1
# Dec 22, 2012 - v2: updated cutoffs to RD Model deposit averages and SP optimum, added Reactive split to Low Grade, reversed DESTC order
# May 15, 2013 - v2.01: updated cutoffs for mid-2013
# July 7, 2014 - v2.02: updated cutoffs for mid-2014
# Nov 11, 2014 - v3: added exception for Qanaiyaq High Ag and moved concentrate tonnage calculation from "Model Calcs" for same, added VALS ($/sec) calculation
# Nov 16, 2014 - v3.01: updated cutoffs for eoy-2014
# Nov 22, 2014 - v4: added LGO rehandle incremental cost to new mill_co_RH array; changed REACT criteria for LGO to be more conservative; Removed REASS from DESTC classification
#                    added overwrite of Pb metallurgical parameters if Oxide Ore
# Dec 20, 2014 - v5: added exception to High & Low grade DESTC assignment to exclude Non-sulphide "ore" from reclassification if script rerun
# Jan 4, 2015 - v6: added high Barite lower cut-off material to Mill Feed (DESTC = 1); added test to ensure ore goes to highest profit float circuit (sulfide or non-sulfide)
# Mar 23, 2015 - v7: converted to $/s allocation basis; incorporated dilution coding & waste reclassification; added logic for Resource Classification filtering
# May 8, 2015 - v8: incorporated VALB calculation and escalation costs from NSR script (renamed this script to DEST from DESTC due to this combining of functions); removed mill_co_RH array
#                   added classification for DILFG and matching to R&R; updated mining costs for mid-2015
# June 17, 2015 - v8.01: corrected VALB calc application logic; moved all concentrate calculation and VALT and VALS recalculation to end of script;
# July 17, 2015 - v8.02: modified code for haulEsc inclusion in NSR script; removed VALT and VALS recalculation at end of script and added calculation for Net $/t item (NETT)
# July 27, 2015 - v9: separated out VALB calculation to be run independantly; commented out DEP slab access (use Qanaiyaq path check)
# Nov 20, 2015 - v10: modified to use MPT (minutes-per-tonne) instead of TPH (tonnes-per-hour)
# Dec 28, 2015 - v10.01: added DPS ($/s) cutoff spinner; added dilution selectivity for DESTR and modified code to calc concentrate based on diluted or undiluted destination code
# Mar 24, 2016 - v10.02: added check for geology in air; set Oxide "Ore" always defined; renamed Non-Sulphide items to Oxide; transfered in GNDHR from ModelCalcs
# Apr 9, 2016 - v10.03: updated costs for mid-2016 (based on 2016 O-LOM c/o); added indirect_cost cost to ensure Breakeven at $0/t is correct; added text log file for script execution
# May 17, 2016 - v10.04: enabled Zn conc, Pb conc, Grind Hrs, calculation for all blocks > $0/s
# May 27, 2016 - v10.05: updated costs for mid-2016 (based on 2017 S-LOM c/o)
# Oct 28, 2016 - v10.06: included net mining cost differential in VALS calculations; pulled stockpile (LGO or OX) mining cost out of NETT as needs to be specified in MSSO; moved Date-Time to start of text message and added user name;
# Dec 7, 2016 - v10.06VIP: changed mining, milling, and indirect_cost costs for 2017 LOM-O schedule
# Jan 24, 2017 - V10.07VIP: added Blastability index
# Mar 31, 2017 - V10.08VIP: updated mine, milling, and O/H costs; added logic for separate tailings cost inclusion
# June 25, 2017 - V10.08.01VIP: added ORCT4 filtering by DESTC
# July 1, 2017 - V10.08.02VIP: added filter for computation to only apply to PERLT < 1
# July 23, 2017 - V10.08.03VIP: added GEOL code 19 to groups (higher iron version of GEOL code 8)
# Sept 17, 2017 - V10.08.04VIP: added destination code of 9 for High Copper Weathered "waste" (not economic based)
# Jan 23, 2018 - V11.00: converted indirect cost from tonnage basis to time basis as independent of tonnage (i.e. actually $ per year); made code 9 (High Copper Weathered) economic based;
#                        modified haulage increment to apply both below and above index bench; removed REACT logic due to reactivity model update in ModelCalcs (2016 version);
#                        updated all costs (mining, milling, G&A, etc.) to EcM_20180122;
# Feb 6, 2018 - V11.01: logic bug fix for DESTC coding of OX and WX;
# Feb 11, 2018 - V11.02: altered Milling Options logic; revised NETT for stockpiles to include mining cost;
# [Apr 4, 2018]          changed ORCT4 coding to include waste (relocated all ORCT4 logic from ModelCalcs to this script);
# Apr 8, 2018 - V11.10: added additional DEST code of MG=10 for temporary stockpiling of Baritic Medium Grade from Aqqaluk (this is handled as HG for the purposes of dilution);
# Apr 9, 2018 - V11.11: all "MG" from Aqqaluk stockpiled instead of just Ba material;
# May 2, 2018 - V11.11.1: reordered logic in last section of code "Concentrate and NET $/t calculations based on DESTx" to accommodate unusual situation of Destination code MG being assigned in a block with an unassigned year;
# [June 2, 2018]          added "Failed!" to output text file if run incomplete;
# [July 4, 2018]          modified VALB calculation for LG material discounting;
# [July 9, 2018]          moved GNDHR calculation back to ModelCalcs script;
# [Oct 17, 2018]          replaced YEAR with PERLT as MSSO periods of variable size;
# Dec 30, 2018 - V11.50: added third c/o for LG-PR to HG; split 10MG code into 10MG-N and 11MG-PR; revised ORCT4 coding to not include MG in primary coding; added option to have an array of cutoffs (for R&R change tracking);
#                        moved throughput and power escalator programming in from NSR script; removed references to GEOL codes 9, 19, 30, 31, and 34 as no longer used, changed GEOL code for Air from 50 to 0;
#                        changed GEOL groupings to 2D arrays by deposit;
# Jan 31, 2019 - V11.50.1: changed GEOL codes for QAN2016 model;
# Feb 15, 2019 - V11.50.2: updated costs for LOM 2020; removed NETT and added OPCST calculation;
# Apr 6, 2019 - V11.50.3: revised costs for LOM2020 based on newer (March 15) version of economic spreadsheet; set WX destination assignment to be selectable by maximum value or by Sulfide Mill preference (maximizeWX = T/F, default = F);
# Apr 20, 2019 - V11.50.4: revised costs for LOM2020 based on Capital reorganization in Econ workbook; added maximum Ba and Fe grades to MGO selection criteria;
#          [May 11, 2019]: updated array cutoff to LOMO2020 sequence;
# May 18, 2019 - V11.50.5: revised costs for 5-YR Plan based on 'EcM20190517_12-7.5p12_2.10rem_20190507.xlsx' parameters
# Feb 17, 2020 - V11.51: updated costs for LOM2021 based on 'EcM LOM 2021 - 20200217.xlsx' R&R parameters; set to maximize Weathered Mill feed over Sulfide feed when more valuable;
# Feb 27, 2020 - V11.51.1: removed discounting on Weathered Mill feed selection as not accounting for total material quantity;
# Mar 1, 2020 - V11.51.2: simplified OpCost calculation logic and changed OpCost value to match DESTC assignment; added OPCST and VALS recalc (at end) when dilution changes classification;
# Mar 27, 2020 - V11.51.3: added extra flotation cost for Oxide Pb-Ag;
# Apr 24, 2020 - V11.51.4: updated costs for 2021LOM-O based on 'EcM LOM 2021 - 20200424.xlsx' R&R parameters;
# Jul 19, 2020 - V11.51.5: updated costs for 2021-5YR based on 'EcM LOM 2021 - 20200719.xlsx' R&R parameters;
# Oct 30, 2020 - V11.51.6: added QWXFG=1 and WXFG=1 if MET set to 4 in VALS_WX calculation section;
# Feb 28, 2021 - V11.52.0: updated costs for 2022 LOM based on 'EcM LOM 2022 - 20210228.xlsx' R&R parameters; changed ORCT4 Zn binning to 0-15% Zn_LG, 15-25% Zn_MG and >25% Zn_HG (previously 0 to 10%, 10 to 20%, >20%);
# Jan 21, 2022 -V11.52.1 updated the costs for the 2023 LOM based on ' EcM LOM 2023- 20220119.xlsx parameters;
# Feb 17, 2022 -v11.52.1 updated the cost from the 2023 LOM (Jan 21, 2022 values are over-written with actual numbers from the EcM LOM)
# April 13, 2022-v11.52.2- Changing the name from v11.52.1 to 11.52.2 for clarity, and making it distinct, Note that v11.52.3 is changed QAN codes, which is still in progress. 
# Feb 9, 2023 -v11.52.4 Updated the costs for the LOM 2024
# July 3, 2023-v11.52.5 Updated the costs for the 5YBP 2024
# Feb 26, 2024 - v11.52.5_QAN: QAN22v6 (updated S) model update
#==============================================================================
# Mill and mill feed option codes are:
#  0 - LG stockpiled and std VALB {1-cutoff}(HG to mill; LG-N to LG SP; OX & WX to SPs)
#  1 - MG stockpiled {2-cutoff} (HG & Qan MG to mill; Aqq MG to MG SP; LG-N to LG SP; OX & WX to SPs)
#  2 - MG & LG to HG {3-cutoff} (HG, MG, ~LG-PR to mill; LG-N to LG SP; OX & WX to SPs)
#  3 - VALB at HG cutoff {1-cutoff}(HG to mill; LG-N to LG SP; OX & WX to SP)
#  4 - VALB Mill OX {1-cutoff}(HG to mill; LG-N to LG SP; OX to Mill; WX to SP)
#  5 - VALB Mill WX {1-cutoff}(HG to mill; LG-N to LG SP; OX to SP; WX to Mill)
#  6 - VALB Mill OX & WX {1-cutoff}(HG to mill; LG-N to LG SP; OX & WX to Mill)

# VALB calculation option codes are:
#  1 - not calculated
#  2 - M&I basis
#  3 - MI&I basis
#  4 - MII&B basis
# Notes: 1) when VALB calculation is set all other parameters are not calculated, i.e. skipped
#        2) VALB starts at 1 to use VALBtype code as RESCL category filter

# Waste ARD "WARDC" codes are:
#  0 - Possibly Reactive (SHC of 5 or greater)
#  1 - Low Reactive
#  2 - Construction
#  3 - Cover

# Dilution flag "DILFG" codes are:
#   0 - Sulphide Mill Feed from waste - Dilution kernel
#   1 - Sulphide Mill Feed unchanged
#   2 - Waste unchanged
#   3 - Waste from Mill Feed - Dilution kernel
#   4 - Sulphide Ore from waste - Noise reduction - Horseshoe shape
#   5 - Sulphide Ore from waste - Noise reduction - Parallel lines
#   6 - Sulphide Ore from waste - Noise reduction - Corner
#   7 - Waste from Sulphide Ore - Noise reduction - Horseshoe shape
#   8 - Waste from Sulphide Ore - Noise reduction - Parallel lines
#   9 - Waste from Sulphide Ore - Noise reduction - Corner
#  10 - Sulphide Ore from Sulphide Ore - Noise reduction - Horseshoe shape
#  11 - Sulphide Ore from Sulphide Ore - Noise reduction - Parallel lines
#  12 - Sulphide Ore from Sulphide Ore - Noise reduction - Corner
#  13 - Waste from Waste - Noise reduction - Horseshoe shape
#  14 - Waste from Waste - Noise reduction - Parallel lines
#  15 - Waste from Waste - Noise reduction - Corner
#  16 - Waste from Sulphide HG and LG-N - R&R criteria
#  17 - Waste from Sulphide LG-PR - R&R criteria
#  18 - Waste from Oxide 'Ore' - R&R criteria
#  19 - Waste from Weathered 'Ore' - R&R criteria

# Reserve & Resource destination "DESTR" codes are:
# DESTR   Material                   RESCL  Class
#   0     Waste                      all    All
#   1     Sulphide HG-mill feed      1 & 2  Measured & Indicated
#   2     Sulphide HG-mill feed      3      Inferred
#   3     Sulphide LGn-stockpiled    1 & 2  Measured & Indicated
#   4     Sulphide LGn-stockpiled    3      Inferred
#   5     Sulphide LGpr              1 & 2  Measured & Indicated
#   6     Sulphide LGpr              3      Inferred
#   7     Oxide Pb-Ag                1 & 2  Measured & Indicated
#   8     Oxide Pb-Ag                3      Inferred
#   9     Weathered Zn-Cu            1 & 2  Measured & Indicated
#   10    Weathered Zn-Cu            3      Inferred
#   11    Waste HG & LGn (reclassed) 4 & 5  Blue Sky & Unlikely
#   12    Waste LGpr (reclassed)     4 & 5  Blue Sky & Unlikely
#   13    Waste OX (reclassed)       4 & 5  Blue Sky & Unlikely
#   14    Waste WX (reclassed)       4 & 5  Blue Sky & Unlikely
# Note: classifications 7 to 10 only exist if oxide/weathered milling is enabled

#==============================================================================
# Constants
#==============================================================================

# items to get from model
itemlist = ["PERLT","DEP","GEOL","DESTC","DESTD","DESTR","DILFG","WARDC","STZN","STPB","STFE","STBA","ZNGRD","ZNREC","PBGRD","PBREC","ODENM","ZNCON","PBCON","TAILS","MPT","SESAG","SEBM","RESCL","OPCST","BAC","ORCT2","ORCT4","FLAG2"] # or FLAG1?
itemlistQanAdd = ["PBROX","PBGOX","ZNRWX","ZNGWX","MET","QWXFG","WXFG"]
# items written to model
# DESTC, DESTD, DESTR, DILFG, ZNCON, PBCON, TAILS, VALSx, VALBx, NETT, BAC, ORCT4

# GEOL code groupings (2D array is [M,A,P,Q])
Air = 0
Baritic = [[15, 16], [15, 16], [7], [51,52,53,54,56]]
Construction = [[3, 4], [3, 4], [3, 4], [200]]
Black_Shale = [[25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [25, 26, 27, 32, 33], [201, 202, 203]]
Non_Baritic = [[1, 2, 6, 8, 11, 12, 13, 14, 18], [1, 2, 6, 8, 11, 12, 13, 14, 18], [10, 20, 21], [10,11,12,13,14,16,20,21,22,23,24,26,40,41,42,43,44,46,60, 61,62,63,64,66]]

# Destination codes (DESTC, DESTD) for materials are:
HG    = 1  # High Grade (Direct Mill Feed)
LG_N  = 2  # Low Grade Non-reactive
LG_PR = 3  # Low Grade Possibly Reactive
W_PR  = 4  # Waste Possibly Reactive
W_N   = 5  # Waste Non-reactive
W_CN  = 6  # Waste Construction
W_CV  = 7  # Waste Cover
SP_OX = 8  # Oxide (High Pb/Ag)
SP_WX = 9  # Weathered (High Cu/Zn)
MG_N  = 10 # Middle Grade Non-reactive
MG_PR = 11 # Middle Grade Possibly Reactive

# dilution kernel matrix (initialization) for 3x3 area
# 6 7 8
# 3 4 5
# 0 1 2
MTX = [0]*9

# mining and milling cost (array is [M,A,P,Q])
mine_waste_cost = [5.96, 5.96, 5.96, 5.43] # $/t waste rock
mine_ore_cost = [5.88, 5.88, 5.88, 5.61]   # $/t ore rock
mill_cost = [28.48, 28.48, 28.48, 26.55]   # $/t mill feed
mill_oxide = 25.92                         # $/t Oxide Pb-Ag mill feed
tailsCostPerTonne = 7.94                  # $/t tailings, includes dam construction
rehandle_cost =0.206                       # $/t mill feed, incremental rehandle cost for extra tram distance from LGO (or OXID) stockpile to crusher
indirect_cost = 23711.53                   # $/hr grinding, based on total LOM G&A cost divided by total LOM mill grinding hours (could also be annual G&A cost divided by Available Mill Operating Hours per year, i.e. 365 x 24 x 93.5%)

# cost escalators for grinding energy and throughput (array is [M,A,P,Q])
averagePower = 18.7 # kwh/t (SAG mill + Ball mill specific energy)
powerCost = 0.223 # $/kwh
comminutionCost = [10.02, 10.02, 10.02, 8.49] # $/t, crushing and grinding (no labor)
averageTPH = [500, 500, 500, 590]  # tph, plan average  from last similar LOM schedule (2023 onwards LOM 5-YR, Taken from MP tab for AQQ and QAN)

# cost escalator for elevation (array is [M,A,P,Q])
haulIncrLU = 0.0159 # $/t/bench for benches above index ("Loaded Up"), +0.303min/bench, excludes horizontal distance
haulIncrLD = 0.0184 # $/t/bench for benches below index ("Loaded Down"), +0.351min/bench, includes horizontal distance
haulIncrBench = [17, 17, 17, 12] # bench index [925,925,925,1300], median tonnage bench from previous year {Qan is access bench}

# default operating cutoff
DPScutoff = 1.00  # $/s, this is primary (or LG-N) cutoff iterated when maximizing NPV
DPScutoffMG = 20.0 # $/s, this is secondary (or LG-PR) cutoff when maximizing NPV in LG-PR milling options
DPScutoffLG = 0.00 # $/s, this is tertiary (or LG-PR to HG) cutoff when maximizing NPV in partial LG-PR milling options
# or operating cutoff arrays set to 2020LOM-O cutoffs by period, for End-of-2020 R&R change tracking
#           YEAR  2019   2020                    2021                   2022                 2023      2024     2025+(by year)
#           PERLT    0    1     2     3     4     5     6     7     8     9   10   11   12   13   14   15   16   17   18   19   20   21   22   23   24   25   26   27   28
DPScutoff_ar =   [12.00,12.00,12.00,12.00,12.00,12.00,12.00,12.00,12.00,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10] # $/s, this is primary (or LG-N) cutoff iterated when maximizing NPV, by year (starts YR0 same as YR1)
DPScutoffMG_ar = [ 7.00, 7.50, 7.50, 7.50, 7.50, 7.50, 7.50, 7.50, 7.50,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10,2.10] # $/s, this is secondary (or LG-PR) cutoff when maximizing NPV in LG-PR milling options, by year (starts YR0 same as YR1)

# Qanaiyaq Weathered value realization
maximizeWX = True      # if False then maximize Sulfide Mill feed; if True then maximize Weathered Mill feed, i.e. if a Bulk Concentrate gives a higher cash flow than Zinc & Lead Concentrates then make a Bulk Concentrate

#==============================================================================
# Panel 1
#==============================================================================

file15 = StringRTV(name="file15")
pickBench = IntegerRTV(name="pickBench", value=58)

pickDPScutoff = FloatRTV(name="pickDPScutoff", value=DPScutoff)
pickDPScutoffMG = FloatRTV(name="pickDPScutoffMG", value=DPScutoffMG)
pickDPScutoffLG = FloatRTV(name="pickDPScutoffLG", value=DPScutoffLG)

NGPmill = IntegerRTV(name="millFlag", value=0)
MILL_FUNCTIONS = [
   "0-LG stockpiled / VALB breakeven {1-cutoff} (HG to mill; LG-N to LG SP; OX & WX to SPs)","1-MG stockpiled {2-cutoff} (HG & Qan MG to mill; Aqq MG to MG SP; LG-N to LG SP; OX & WX to SPs)",
   "2-MG & LG to HG {3-cutoff} (HG, MG, ~LG-PR to mill; LG-N to LG SP; OX & WX to SPs)","3-VALB HG cutoff is margin {1-cutoff} (HG to mill; LG-N to LG SP; OX & WX un-milled)",
   "4-VALB Mill OX {1-cutoff} (HG to mill; LG-N to LG SP; OX to SP; WX un-milled)","5-VALB Mill WX {1-cutoff} (HG to mill; LG-N to LG SP; OX un-milled; WX to SP)",
   "6-VALB Mill OX & WX {1-cutoff} (HG to mill; LG-N to LG SP; OX & WX to SPs)"
   ]
millFunction = IntegerRTV(name="millFunction")

NGPvalb = IntegerRTV(name="valbFlag", value=0)

VALB_FUNCTIONS = ["0-not a VALB run","1-M&I  (Indicated pit)","2-MI&I  (Inferred pit)","3-MII&B  (Blue-sky pit)                                            "]
valbFunction = IntegerRTV(name="valbFunction")

NGPdr = IntegerRTV(name="drFlag", value=0)
DR_FUNCTIONS = ["0-yes, DESTx = DESTD  (reporting & scheduling)","1-no, DESTx = DESTC  (sensitivity analysis only)  "]
drFunction = IntegerRTV(name="drFunction")

NGPdd = IntegerRTV(name="ddFlag", value=0)
DD_FUNCTIONS = ["0-not filtered  (Ops scheduling)","1-M&I  (R&R scheduling)","2-MI&I  (R&R reporting)                                          "]
ddFunction = IntegerRTV(name="ddFunction")

NUM_ITEMS = 1
ModelItems = [(StringRTV(name="item1" + str(i))) for i in range(NUM_ITEMS)]
ModelLabels = [("$/t var:") for i in range(NUM_ITEMS)]

NGPperiod = IntegerRTV(name="perFlag", value=0)
PERLT_FUNCTIONS = ["0-no, apply to all blocks", "1-yes, apply only to unassigned periods", "2-yes, use prestored array of cutoffs (R&R change tracking)"]
perFunction = IntegerRTV(name="perFunction")

class DefineModelFile(GPanel):

   def makewidgets(self):
      self.makeFilePickers()
      self.makeItems()
      objsignal.listen(file15, "onChange()", self, self.onFile15Change)
      self.onFile15Change(file15)
      self.makeBenchSpinner()
      self.makeDPSSpinner()
      self.makeDPSMGSpinner()
      self.makeDPSLGSpinner()
      self.makeMillFlag()
      self.makeVALBFlag()
      self.makeDRFlag()
      self.makeDDFlag()
      self.makePeriodFlag()

   def makeFilePickers(self):
      grp = GGroup(self, text="Choose model file")
      grp.pack(anchor=NW, pady=2, padx=2, ipadx = 2, ipady=2)
      item15 = cmpsys.getpcf().filelistbytype(15)
      cbs = GComboBox(grp.interior(), items=item15, rtv=file15)
      lbls = GLabel(grp.interior(), text="Name of 3D block model:")
      gtools.stdwidgetcolumns([lbls], [cbs])
      self.remember([cbs])

   def makeItems(self):
      grp = GGroup(self, text="Get VALT from item")
      grp.pack(side = 'top', anchor=W,pady=2, padx=2)
      self.reqrtvs = ModelItems
      self.reqcbs = gtools.makewidgets(grp.interior(), GComboBox, len(self.reqrtvs), list_rtv=self.reqrtvs)
      lbls = gtools.makewidgets(grp.interior(), GLabel, len(ModelLabels), list_text=ModelLabels)
      gtools.stdwidgetcolumns(lbls, self.reqcbs)
      self.remember(self.reqcbs+lbls)

   def onFile15Change(self, file15rtv):
      if len(file15rtv.get())>1:  # make sure there is a model name
         items = cmpsys.getpcf().itemlist(file15rtv.get())
         for cb in (self.reqcbs):
            cb.configure(items=items)

   def makeBenchSpinner(self):
      grp = GGroup(self, text="Lowest bench #")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      benchspin = GSpinner(grp.interior(), min = 1, max = 122, rtv = pickBench)
      benchspin.pack(side='top', anchor=W, padx=15, pady=4)
      self.remember([benchspin])

   def makeDPSSpinner(self):
      grp = GGroup(self, text="$/s cutoff for HG (mandatory)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      DPSspin = GSpinner(grp.interior(), min = 0.0, max = 20.0, rtv = pickDPScutoff)
      DPSspin.pack(side='top', anchor=W, padx=80, pady=4)
      self.remember([DPSspin])

   def makeDPSMGSpinner(self):
      grp = GGroup(self, text="$/s cutoff for MG (optional)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      DPSMGspin = GSpinner(grp.interior(), min = 0.0, max = 20.0, rtv = pickDPScutoffMG)
      DPSMGspin.pack(side='top', anchor=W, padx=80, pady=4)
      self.remember([DPSMGspin])

   def makeDPSLGSpinner(self):
      grp = GGroup(self, text="$/s cutoff for LG (optional)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      DPSLGspin = GSpinner(grp.interior(), min = 0.0, max = 20.0, rtv = pickDPScutoffLG)
      DPSLGspin.pack(side='top', anchor=W, padx=80, pady=4)
      self.remember([DPSLGspin])

   def makeMillFlag(self): # Assign milling destination(s) and mill feed materials
      grp = GGroup(self, text="Mills and mill feeds")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      rbut = GRadio(grp.interior(), items=MILL_FUNCTIONS, rtv=millFunction)
      rbut.pack(anchor=NW, padx=4, pady=4)
      self.remember([rbut])

   def makeVALBFlag(self): # Calculate block values for L-G pit design or not, and if so, base on M&I (Reserve pit), MI&I (Resource pit), or MII&B (Blue Sky pit)
      grp = GGroup(self, text="VALB basis  (for use in MS-EP)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      rbut = GRadio(grp.interior(), items=VALB_FUNCTIONS, rtv=valbFunction)
      rbut.pack(anchor=NW, padx=4, pady=4)
      self.remember([rbut])

   def makeDRFlag(self): # Assigning DESTR based on requirement: diluted for published R&R, undiluted for R&R sensitivity analysis
      grp = GGroup(self, text="Dilution (mills option 0 to 2)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      rbut = GRadio(grp.interior(), items=DR_FUNCTIONS, rtv=drFunction)
      rbut.pack(anchor=NW, padx=4, pady=4)
      self.remember([rbut])

   def makeDDFlag(self): # Assigning DESTD for HG & LG_N based on schedule requirement: LOM plan (all resource classes are OK) or R&R report plan (only M&I resource classes are OK)
      grp = GGroup(self, text="RESCL filter applied to DESTx (mills option 0 to 2)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      rbut = GRadio(grp.interior(), items=DD_FUNCTIONS, rtv=ddFunction)
      rbut.pack(anchor=NW, padx=4, pady=4)
      self.remember([rbut])

   def makePeriodFlag(self):
      grp = GGroup(self, text="Period filter? (mills option 0 to 2)")
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
   print pcfpath

   # calculate block volume
   pcf = cmpsys.getpcf()
   blockVolume = pcf.dx()*pcf.dy()*pcf.dz()

   # get ending Bench from panel variable
   lowestBench = pickBench.get()
   minColumn, minRow, minLevel = 1, 1, 1
   maxColumn, maxRow, maxLevel = pcf.nx(), pcf.ny(), min(lowestBench, pcf.nz())
##   minColumn, minRow, minLevel = 56, 88, 15  # for debugging
##   maxColumn, maxRow, maxLevel = 56, 88, 15  # for debugging

   # check if path to a Qanaiyaq model
   isQanaiyaq = "QAN" in pcfpath or "qan" in pcfpath or "Qan" in pcfpath
   if isQanaiyaq:
      msgText = "\n  Qanaiyaq model "+file15.get()+" in "+projdir
      itemlist.extend(itemlistQanAdd) # add oxide and weathered metallurgy parameters to model item list
   else: # not Qanaiyaq
      msgText = "\n  Aqqaluk model "+file15.get()+" in "+projdir
   print msgText
   PyLogFile.write(msgText)

   # get AMR storage variable name from panel and append to "itemlist", including placeholders for Qanaiyaq variables and corresponding VALS and VALB items
   for item in ModelItems:
      if item.get() != '':
         # get sulphide item, VALTx, and append
         VALTitem = item.get()
         itemlist.append(VALTitem)
         # turn VALTx into VALSx and append
         VALSitem = VALTitem.replace("T","S")
         itemlist.append(VALSitem)
         # turn VALTx into VALBx and append
         VALBitem = VALTitem.replace("T","B")
         itemlist.append(VALBitem)
         if isQanaiyaq:
            # turn VALTx into VLTOx and append
            VLTOitem = VALTitem.replace("ALT","LTO")
            itemlist.append(VLTOitem)
            # turn VALTx into VLTWx and append
            VLTWitem = VALTitem.replace("ALT","LTW")
            itemlist.append(VLTWitem)
         break

   # select available mills and feed types
   millingOption = millFunction.get()
   msgText = "\n  Option #1, Mill feeds:       "+MILL_FUNCTIONS[millingOption]+"\n"
   print msgText
   PyLogFile.write(msgText)

   # get $/s OP and LG-PR cutoffs
   DPScutoff = pickDPScutoff.get()
   if millingOption <=0 or millingOption >=3: # only one cutoff; set cutoffs equal
      DPScutoffMG = DPScutoff
      DPScutoffLG = DPScutoff
   else: # multiple cutoffs; ensure third c/o <= second c/o <= first c/o
      DPScutoffMG = pickDPScutoffMG.get()
      DPScutoffMG = min(DPScutoff, DPScutoffMG)
      DPScutoffLG = pickDPScutoffLG.get()
      DPScutoffLG = min(DPScutoffMG, DPScutoffLG)

   # get DESTR classification basis (diluted or undiluted)
   DESTRdiluted = drFunction.get()<=0
   if DESTRdiluted:
      DESTname = "DESTD"
   else:
      DESTname = "DESTC"

   # get VALBtype to determine if VALB calculation only run
   VALBtype = valbFunction.get() + 1 # add 1 to use VALBtype code as RESCL category filter for VALB computation
   msgText = "  Option #2, VALB calculation: "+VALB_FUNCTIONS[VALBtype-1]+"\n"
   print msgText
   PyLogFile.write(msgText)

   if VALBtype <= 1: # not a VALB calculation run
      msgText = "  Option #3, Dilution enabled: "+DR_FUNCTIONS[not DESTRdiluted]+"\n"
      print msgText
      PyLogFile.write(msgText)
      filterDEST = ddFunction.get()
      msgText = "  Option #4, RESCL filter:     "+DD_FUNCTIONS[filterDEST]+"\n"
      print msgText
      PyLogFile.write(msgText)

      # determine if calculations filtered by period
      period_filter = perFunction.get()
      if period_filter >= 2:
         filter_by_period = True
         filter_by_period_ar = True
         msgText = "  Apply cutoffs by period using stored array\n"
      elif period_filter >= 1:
         filter_by_period = True
         filter_by_period_ar = False
         msgText = "  Apply only to unassigned periods\n"
      else: # period_filter = 0
         filter_by_period = False
         filter_by_period_ar = False
         msgText = "  Apply to all blocks\n"
      print msgText
      PyLogFile.write(msgText)

      if filter_by_period_ar:
         msgText = "  DESTC varied by year based on $/s cutoffs for HG and MG defined in stored arrays\n"
      else:
         if millingOption == 1: # 2 cutoff option
            msgText = "  DESTC based on cutoffs of $"+str(DPScutoff)+"/s for HG and $"+str(DPScutoffMG)+"/s for MG\n"
         elif millingOption == 2: # 3 cutoff option
            msgText = "  DESTC based on cutoffs of $"+str(DPScutoff)+"/s for HG, $"+str(DPScutoffMG)+"/s for MG, and $"+str(DPScutoffLG)+"/s for LG-PR\n"
         else:
            msgText = "  DESTC based on a cutoff of $"+str(DPScutoff)+"/s for HG\n"
      print msgText
      PyLogFile.write(msgText)

      if isQanaiyaq:
         msgText = "  $/s values stored in "+VALSitem+" and obtained from $/t values in "+VALTitem+", "+VLTOitem+", and "+VLTWitem+"\n"
      else:
         msgText = "  $/s values stored in "+VALSitem+" and obtained from $/t value in "+VALTitem+"\n"
      print msgText
      PyLogFile.write(msgText)
   else: # a VALB calculation run
      msgText = "  Option #3, DESTR dilution:   inactive\n"
      print msgText
      PyLogFile.write(msgText)
      msgText = "  Option #4, RESCL filter:     inactive\n"
      print msgText
      PyLogFile.write(msgText)
      if millingOption <= 3: # Sulphide milling only
         msgText = "  $/block values stored in "+VALBitem+" and obtained from $/t value in "+VALTitem+"\n"
      elif millingOption <= 4: # High Lead Oxide considered Ore for pit design
         msgText = "  $/block values stored in "+VALBitem+" and obtained from $/t values in "+VALTitem+" and "+VLTOitem+"\n"
      elif millingOption <= 5: # Weathered High Copper considered Ore for pit design
         msgText = "  $/block values stored in "+VALBitem+" and obtained from $/t values in "+VALTitem+" and "+VLTWitem+"\n"
      else: # millingOption = 6; High Lead Oxide and Weathered High Copper considered Ore for pit design
         msgText = "  $/block values stored in "+VALBitem+" and obtained from $/t values in "+VALTitem+", "+VLTOitem+", and "+VLTWitem+"\n"
      print msgText
      PyLogFile.write(msgText)

      if millingOption == 3: # HG cutoff margin option, uses DPScutoff as margin
         msgText = "  VALB ore based on HG cutoff of $"+str(DPScutoff)+"/s instead of $0/s\n"
      else:
         msgText = "  VALB ore based on a $0/s margin\n"
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
            if VALBtype > 1: # a VALB calculation run only
               # == VALB assignment ==
               # traverse the slab, get values, calculate, and set the new values
               # note that array implementation of cutoffs by year is not incorporated into VALB calculation as VALB is independant of the year
               # L-G calculation only based on undiluted blocks as one can not start a "cone" on a diluted waste block
               for r in xrange(rows):
                  for c in xrange(cols):
                     GEOL = slab["GEOL", l, r, c]
                     if GEOL > Air: # not air
                        # grab values
                        d = int(slab["DEP", l, r, c] - 1) # array index starts at 0
                        WARDC = slab["WARDC", l, r, c]
                        ODENM = slab["ODENM", l, r, c]
                        RESCL = slab["RESCL", l, r, c]
                        MPT = slab["MPT", l, r, c]     # min/t
                        TPH = 60.0/MPT                 # t/hr
                        SEsag = slab["SESAG", l, r, c]
                        SEbm = slab["SEBM", l, r, c]
                        AMR = slab[VALTitem, l, r, c]
                        STZN = slab["STZN", l, r, c]
                        ZNREC = slab["ZNREC", l, r, c]
                        ZNGRD = slab["ZNGRD", l, r, c]
                        STPB = slab["STPB", l, r, c]
                        PBREC = slab["PBREC", l, r, c]
                        PBGRD = slab["PBGRD", l, r, c]

                        # calculate operating cost escalators and base operating cost ($/t)
                        powerEsc = (SEsag + SEbm - averagePower) * powerCost  # grinding power cost escalator, (+) is increased cost
                        throughputEsc = comminutionCost[d]*(averageTPH[d]/TPH - 1)  # throughput rate cost escalator, (+) is increased cost
                        haulEsc = max((haulIncrBench[d] - b) * -haulIncrLU, (haulIncrBench[d] - b) * haulIncrLD)  # haulage cost adjustment above/below median bench (either direction an increase); (+) is increased cost
                        OpCost_mill_noTails = haulEsc + (mill_cost[d] + powerEsc + throughputEsc) + indirect_cost/TPH

                        # calculate Sulphide operating cost and Mill cutoff ($/t)
                        Concentrate = (STZN * ZNREC / ZNGRD + STPB * PBREC / PBGRD)/100.0
                        tails_cost = (1.0 - Concentrate) * tailsCostPerTonne
                        OpCost_mill_SU = OpCost_mill_noTails + tails_cost
                        MillCO_SU = OpCost_mill_SU + mine_ore_cost[d] - mine_waste_cost[d]

                        if millingOption != 3:  # normally this case would be for millingOption=0, i.e. conventional breakeven cutoff
                           block_is_HGore = RESCL <= VALBtype and AMR >= MillCO_SU
                           block_is_LGore = False
                        else: # millingOption = 3, use HG c/o as threshold
                           VALS_block = (AMR - MillCO_SU) / MPT /60  # $/sec for block
                           block_is_HGore = RESCL <= VALBtype and VALS_block >= DPScutoff
                           if block_is_HGore:
                              block_is_LGore = False
                           else:
                              VALS_block_LG = VALS_block - rehandle_cost / MPT /60  # $/sec for block for stockpile material
                              block_is_LGore = RESCL <= VALBtype and VALS_block_LG >= 0 and WARDC > 0  # only non-reactive is stockpiled for eventual recovery

                        NET_SU = AMR - OpCost_mill_SU - mine_ore_cost[d]
                        if block_is_HGore:
                           workVALB = NET_SU * blockVolume * ODENM
                        elif block_is_LGore:
                           workVALB = 0.70 * (NET_SU - rehandle_cost) * blockVolume * ODENM  # discount value to 70% due to delayed realization of value from stockpiling (10 years to reclaim, so 5 years for mid-point of reclaim, at 8% discount) = 1/1.08^5 = 68%
                        else:
                           workVALB = -(mine_waste_cost[d] + haulEsc) * blockVolume * ODENM

                        # additional calculations if secondary mill available for High Pb Oxide and/or Weathered High Cu, thus added value of these ores used in pit generation
                        if isQanaiyaq and millingOption >= 4:
                           # 1) High Lead Oxide
                           AMR_OX = slab[VLTOitem, l, r, c]
                           PBROX = slab["PBROX", l, r, c]
                           PBGOX = slab["PBGOX", l, r, c]
                           # calculate tailings tonnage and cost
                           Concentrate = (STPB * PBROX / PBGOX)/100.0
                           tails_cost = (1.0 - Concentrate) * tailsCostPerTonne
                           # calculate Oxide operating cost and and Mill cutoff ($/t)
                           OpCost_mill_OX = OpCost_mill_noTails + tails_cost + rehandle_cost + mill_oxide
                           MillCO_OX = OpCost_mill_OX + mine_ore_cost[d] - mine_waste_cost[d]

                           # 2) Weathered High Copper
                           AMR_WX = slab[VLTWitem, l, r, c]
                           ZNRWX = slab["ZNRWX", l, r, c]
                           ZNGWX = slab["ZNGWX", l, r, c]
                           # calculate tailings tonnage and cost
                           Concentrate = (STZN * ZNRWX / ZNGWX)/100.0 # Zn basis for Bulk Conc
                           tails_cost = (1 - Concentrate) * tailsCostPerTonne
                           # calculate Weathered operating cost and Mill cutoff ($/t)
                           OpCost_mill_WX = OpCost_mill_noTails + tails_cost + rehandle_cost
                           MillCO_WX = OpCost_mill_WX + mine_ore_cost[d] - mine_waste_cost[d]

                           # revise VALB block value if higher value threshold met
                           if millingOption == 4 or millingOption == 6:
                              NET_OX = AMR_OX - OpCost_mill_OX - mine_ore_cost[d]
                              if RESCL <= VALBtype and NET_OX > 0 and (NET_OX > NET_SU):
                                 workVALB = NET_OX * blockVolume * ODENM
                           if millingOption >= 5: # i.e. 5 or 6
                              NET_WX = AMR_WX - OpCost_mill_WX - mine_ore_cost[d]
                              if RESCL <= VALBtype and NET_WX > 0 and (NET_WX > NET_SU):
                                 workVALB = NET_WX * blockVolume * ODENM

                        # store resulting VALB value
                        slab[VALBitem, l, r, c] = workVALB
                     else: # in air, so just store "no value"
                        slab[VALBitem, l, r, c] = 0.0
               # == end of VALB assignment ==
            else:  # not a VALB calculation run
               # == DESTC assignment ==
               # traverse the slab, get values, calculate, and set the new values
               for r in xrange(rows):
                  for c in xrange(cols):
                     if filter_by_period:
                        PERLT = int(slab["PERLT", l, r, c])
                        if filter_by_period_ar: # use stored array value
                           DPScutoff = DPScutoff_ar[PERLT]
                           DPScutoffMG = DPScutoffMG_ar[PERLT]
                           DPScutoffLG = DPScutoffMG
                           run_calcs = True
                        else: # run with entered cutoff(s) if year not set
                           run_calcs = PERLT < 1
                     else: # run with entered cutoff(s) on all blocks
                        run_calcs = True

                     if run_calcs:
                        GEOL = slab["GEOL", l, r, c]
                        if GEOL > Air:
                           # grab values
                           d = int(slab["DEP", l, r, c] - 1) # array index starts at 0
                           WARDC = slab["WARDC", l, r, c]
                           MPT = slab["MPT", l, r, c] # min/t
                           TPH = 60.0/MPT             # t/hr
                           TPS = 1.0 / (MPT * 60.0)   # t/sec
                           SEsag = slab["SESAG", l, r, c]
                           SEbm = slab["SEBM", l, r, c]
                           AMR = slab[VALTitem, l, r, c]
                           STZN = slab["STZN", l, r, c]
                           ZNREC = slab["ZNREC", l, r, c]
                           ZNGRD = slab["ZNGRD", l, r, c]
                           STPB = slab["STPB", l, r, c]
                           PBREC = slab["PBREC", l, r, c]
                           PBGRD = slab["PBGRD", l, r, c]
                           STFE = slab["STFE", l, r, c]
                           STBA = slab["STBA", l, r, c]

                           # calculate operating cost escalators and base operating cost ($/t)
                           powerEsc = (SEsag + SEbm - averagePower) * powerCost  # grinding power cost escalator, (+) is increased cost
                           throughputEsc = comminutionCost[d]*(averageTPH[d]/TPH - 1)  # throughput rate cost escalator, (+) is increased cost
                           haulEsc = max((haulIncrBench[d] - b) * -haulIncrLU, (haulIncrBench[d] - b) * haulIncrLD)  # haulage cost adjustment above/below median bench (either direction an increase); (+) is increased cost; technically should not be included in $/s calc, but not large and easier to compute here than in MSSO
                           OpCost_mill_noTails = haulEsc + (mill_cost[d] + powerEsc + throughputEsc) + indirect_cost/TPH

                           # calculate Sulphide operating cost and Mill cutoff ($/t)
                           Concentrate = (STZN * ZNREC / ZNGRD + STPB * PBREC / PBGRD)/100.0
                           tails_cost = (1 - Concentrate) * tailsCostPerTonne
                           OpCost_mill_SU = OpCost_mill_noTails + tails_cost
                           MillCO_SU = OpCost_mill_SU + mine_ore_cost[d] - mine_waste_cost[d]

                           # calculate $/s
                           VALS = (AMR - MillCO_SU) * TPS  # $/sec for block for direct mill feed
                           VALS_RH = VALS - rehandle_cost * TPS  # $/sec for block for stockpiled LG as includes rehandle

                           # set model values default for all sulfide materials (adjustment for LG-N as rehandle is included for that material)
                           OPCST_value = OpCost_mill_SU
                           VALS_value = VALS

                           # assign DESTC and write VALS values to slab (check Panel 1 constants for millingOption definitions)
                           if VALS >= DPScutoff or ((millingOption == 1 or millingOption == 2) and VALS >= DPScutoffMG) or (not isQanaiyaq and millingOption == 2 and VALS >= DPScutoffLG and WARDC <= 0): # HG or MG or LG-PR in Aqqaluk
                              workDESTC = HG
                              isMGO = not isQanaiyaq and VALS < DPScutoff and VALS >= DPScutoffMG and STFE < 14 and STBA < 9 # modify MGO based on histograms of MGO stockpile in LOM (9% Ba gives 85% of tonnage, 14% Fe gives 91% of tonnage)
                           else:
                              isMGO = False
                              if VALS_RH >= 0:
                                 if WARDC > 0:
                                    workDESTC = LG_N
                                    # set model values including rehandle cost
                                    OPCST_value = OpCost_mill_SU + rehandle_cost
                                    VALS_value = VALS_RH
                                 else: # LG-PR not otherwise allocated
                                    workDESTC = LG_PR
                              elif WARDC <= 0:
                                 workDESTC = W_PR
                              elif WARDC <= 1:
                                 workDESTC = W_N
                              elif WARDC <= 2:
                                 workDESTC = W_CN
                              else: # WARDC <= 3:
                                 workDESTC = W_CV

                           # if Qanaiyaq deposit then check for possible High Lead Oxide and Weathered High Copper materials
                           if isQanaiyaq:
                              # 1) check if Oxide High Lead-Silver
                              AMR_OX = slab[VLTOitem, l, r, c]
                              PBROX = slab["PBROX", l, r, c]
                              PBGOX = slab["PBGOX", l, r, c]
                              # calculate tailings tonnage and cost
                              Concentrate = (STPB * PBROX / PBGOX)/100.0
                              tails_cost = (1 - Concentrate) * tailsCostPerTonne
                              # calculate Oxide operating cost and and Mill cutoff ($/t), include rehandle cost as assume majority will be stockpiled due to: a) small mill size or b) end-of-life milling
                              OpCost_mill_OX = OpCost_mill_noTails + tails_cost + rehandle_cost + mill_oxide
                              MillCO_OX = OpCost_mill_OX + mine_ore_cost[d] - mine_waste_cost[d]
                              # calculate $/s
                              VALS_OX = (AMR_OX - MillCO_OX) * TPS
                              if VALS_OX >= 0: # then assign to 8-Oxide High Pb-Ag directly as no overlap with regular Sulfide Mill feed
                                 workDESTC = SP_OX
                                 # set model values, includes rehandle cost
                                 OPCST_value = OpCost_mill_OX
                                 VALS_value = VALS_OX
                              else:
                                 # 2) check possibility of Weathered High Zinc-Copper
                                 AMR_WX = slab[VLTWitem, l, r, c]
                                 ZNRWX = slab["ZNRWX", l, r, c]
                                 ZNGWX = slab["ZNGWX", l, r, c]
                                 # calculate tailings tonnage and cost
                                 Concentrate = (STZN * ZNRWX / ZNGWX)/100.0 # Zn basis for Bulk Conc
                                 tails_cost = (1 - Concentrate) * tailsCostPerTonne
                                 # calculate Weathered operating cost and Mill cutoff ($/t), include rehandle cost as assume majority will be stockpiled due to: a) small mill size or b) end-of-life milling
                                 OpCost_mill_WX = OpCost_mill_noTails + tails_cost + rehandle_cost
                                 MillCO_WX = OpCost_mill_WX + mine_ore_cost[d] - mine_waste_cost[d]
                                 # calculate $/s
                                 VALS_WX = (AMR_WX - MillCO_WX) * TPS
                                 if VALS_WX >= 0: # then possiblity exists to assign 9-Weathered High Zn-Cu
                                    # NOTE: WX is about 50/50 PR/N, but stockpiling both Possibly Reactive and Non-reactive material.  Would need to include WARDC if filtering by PR/N...
                                    makeWX = workDESTC >= LG_PR and workDESTC <= W_N # default: transfer to Weathered Milling if Sulfide Milling does not provide a positive cash flow
                                    if maximizeWX: # then additionally transfer to Weathered if provides a higher cash flow than Sulfide Milling
                                       makeWX = makeWX or (workDESTC == LG_N and VALS_WX > VALS_RH) or ((workDESTC <= HG or workDESTC >= MG_N) and VALS_WX > VALS)
                                    if makeWX:
                                       workDESTC = SP_WX
                                       # set model values, includes rehandle cost
                                       OPCST_value = OpCost_mill_WX
                                       VALS_value = VALS_WX
                                       # ensure MET set to Weathered High Zinc-Copper, thus QWXFG and WXFG also set
                                       slab["MET", l, r, c] = 4
                                       slab["QWXFG", l, r, c] = 1
                                       slab["WXFG", l, r, c] = 1

                           # set DESTC, VALS, and OPCST items
                           slab["DESTC", l, r, c] = workDESTC
                           slab[VALSitem, l, r, c] = VALS_value   # this is adjusted at end if destination later reclassified due to dilution
                           slab["OPCST", l, r, c] = OPCST_value   # this is adjusted at end if destination later reclassified due to dilution
                           slab["FLAG2", l, r, c] = isMGO   # used temporarily as boolean for MG possibility flag

                           # for dilution steps, fill DESTD and DILFG with initial values
                           slab["DESTD", l, r, c] = workDESTC
                           if workDESTC <= HG: # set dilution flag =1 only for sulphide mill HG feed
                              slab["DILFG", l, r, c] = 1
                           else:
                              slab["DILFG", l, r, c] = 2
                        else: # in air
                           slab[VALSitem, l, r, c] = 0.0
                           slab["OPCST", l, r, c] = 0.0
                           slab["DESTC", l, r, c] = W_N
                           slab["DESTD", l, r, c] = W_N
                           slab["DILFG", l, r, c] = 2 # not mill feed
               # == end of DESTC assignment ==

               # == DILFG based dilution process (only on HG) ==
               # -- subroutine definitions --
               def WasteTraverse_A():
               # 8-value traverse of the REVISED truncated slab for WASTE diluted to sulphide mill HG ORE
                  for r in xrange(1,rows-1):
                     for c in xrange(1,cols-1):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           # grab working copies of 3x3 area
                           # 6 7 8
                           # 3 4 5
                           # 0 1 2
                           MTX[4] = slab["DILFG", l, r, c]
                           if MTX[4] > 1:  # waste block, has value of 2 (or 3 if dilution modified)
                              MTX[0] = slab["DILFG", l, r-1, c-1]
                              MTX[1] = slab["DILFG", l, r-1, c]
                              MTX[2] = slab["DILFG", l, r-1, c+1]
                              MTX[3] = slab["DILFG", l, r, c-1]
                              MTX[5] = slab["DILFG", l, r, c+1]
                              MTX[6] = slab["DILFG", l, r+1, c-1]
                              MTX[7] = slab["DILFG", l, r+1, c]
                              MTX[8] = slab["DILFG", l, r+1, c+1]
                              if MTX[1] < 2 and MTX[3] < 2 and MTX[5] < 2 and MTX[7] < 2:  # 4 side test
                                 change = True
                              elif MTX[3] < 2 and MTX[1] < 2 and MTX[5] < 2:  # 3 side test-1 (bottom)
                                 change = MTX[0] < 2 and MTX[2] < 2
                              elif MTX[1] < 2 and MTX[3] < 2 and MTX[7] < 2:  # 3 side test-2 (left)
                                 change = MTX[0] < 2 and MTX[6] < 2
                              elif MTX[3] < 2 and MTX[7] < 2 and MTX[5] < 2:  # 3 side test-3 (top)
                                 change = MTX[6] < 2 and MTX[8] < 2
                              elif MTX[1] < 2 and MTX[5] < 2 and MTX[7] < 2:  # 3 side test-4 (right)
                                 change = MTX[2] < 2 and MTX[8] < 2
                              elif MTX[1] < 2 and MTX[7] < 2:                 # 2 side test-1 (opposite, vertical)
                                 change = not(MTX[3] > 1 and MTX[5] > 1) # horizontal line exception
                              elif MTX[3] < 2 and MTX[5] < 2:                 # 2 side test-2 (opposite, horizontal)
                                 change = not(MTX[1] > 1 and MTX[7] > 1) # vertical line exception
                              else:
                                 change = False
                              if change:
                                 slab["DILFG", l, r, c] = 0

               def WasteTraverse_B():
               # 4-value traverse of the REVISED truncated slab for WASTE diluted to sulphide mill HG ORE
                  for r in xrange(1,rows-1):
                     for c in xrange(1,cols-1):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           # grab working copies of 3x3 area
                           # 6 7 8
                           # 3 4 5
                           # 0 1 2
                           MTX[4] = slab["DILFG", l, r, c]
                           if MTX[4] == 2:  # original waste block only
                              MTX[1] = slab["DILFG", l, r-1, c]
                              MTX[3] = slab["DILFG", l, r, c-1]
                              MTX[5] = slab["DILFG", l, r, c+1]
                              MTX[7] = slab["DILFG", l, r+1, c]
                              if MTX[1] < 2 and MTX[3] < 2 and MTX[5] < 2 and MTX[7] < 2:  # 4 side test
                                 change = True
                              elif MTX[3] < 2 and MTX[1] < 2 and MTX[5] < 2:  # 3 side test-1 (bottom)
                                 change = True
                              elif MTX[1] < 2 and MTX[3] < 2 and MTX[7] < 2:  # 3 side test-2 (left)
                                 change = True
                              elif MTX[3] < 2 and MTX[7] < 2 and MTX[5] < 2:  # 3 side test-3 (top)
                                 change = True
                              elif MTX[1] < 2 and MTX[5] < 2 and MTX[7] < 2:  # 3 side test-4 (right)
                                 change = True
                              elif MTX[1] < 2 and MTX[7] < 2:                 # 2 side test-1 (opposite, vertical)
                                 change = not(MTX[3] > 1 and MTX[5] > 1) # horizontal line exception
                              elif MTX[3] < 2 and MTX[5] < 2:                 # 2 side test-2 (opposite, horizontal)
                                 change = not(MTX[1] > 1 and MTX[7] > 1) # vertical line exception
                              else:
                                 change = False
                              if change:
                                 slab["DILFG", l, r, c] = 0

               def OreTraverse_A():
               # 8-value traverse of the truncated slab for sulphide mill HG ORE diluted to WASTE
                  for r in xrange(1,rows-1):
                     for c in xrange(1,cols-1):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           # grab working copies of 3x3 area
                           # 6 7 8
                           # 3 4 5
                           # 0 1 2
                           MTX[4] = slab["DESTC", l, r, c]
                           if MTX[4] <= HG:
                              MTX[0] = slab["DESTC", l, r-1, c-1]
                              MTX[1] = slab["DESTC", l, r-1, c]
                              MTX[2] = slab["DESTC", l, r-1, c+1]
                              MTX[3] = slab["DESTC", l, r, c-1]
                              MTX[5] = slab["DESTC", l, r, c+1]
                              MTX[6] = slab["DESTC", l, r+1, c-1]
                              MTX[7] = slab["DESTC", l, r+1, c]
                              MTX[8] = slab["DESTC", l, r+1, c+1]
                              if MTX[1] > HG and MTX[3] > HG and MTX[5] > HG and MTX[7] > HG:  # 4 side test
                                 change = ((MTX[0] <= HG) + (MTX[2] <= HG) + (MTX[6] <= HG) + (MTX[8] <= HG)) < 3 # diagonal line exception
                              elif MTX[3] > HG and MTX[1] > HG and MTX[5] > HG:  # 3 side test-1 (bottom)
                                 change = MTX[0] > HG and MTX[2] > HG
                              elif MTX[1] > HG and MTX[3] > HG and MTX[7] > HG:  # 3 side test-2 (left)
                                 change = MTX[0] > HG and MTX[6] > HG
                              elif MTX[3] > HG and MTX[7] > HG and MTX[5] > HG:  # 3 side test-3 (top)
                                 change = MTX[6] > HG and MTX[8] > HG
                              elif MTX[1] > HG and MTX[5] > HG and MTX[7] > HG:  # 3 side test-4 (right)
                                 change = MTX[2] > HG and MTX[8] > HG
                              elif MTX[1] > HG and MTX[7] > HG:                  # 2 side test-1 (opposite, vertical)
                                 change = not(MTX[3] <= HG and MTX[5] <= HG) # horizontal line exception
                              elif MTX[3] > HG and MTX[5] > HG:                  # 2 side test-2 (opposite, horizontal)
                                 change = not(MTX[1] <= HG and MTX[7] <= HG) # vertical line exception
                              else:
                                 change = False
                              if change:
                                 slab["DILFG", l, r, c] = 3

               def OreTraverse_B():
               # 8-value traverse of the REVISED truncated slab for sulphide mill HG ORE diluted to WASTE
                  for r in xrange(1,rows-1):
                     for c in xrange(1,cols-1):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           # grab working copies of 3x3 area
                           # 6 7 8
                           # 3 4 5
                           # 0 1 2
                           MTX[4] = slab["DILFG", l, r, c]
                           if MTX[4] == 1: # original ore blocks only
                              MTX[0] = slab["DILFG", l, r-1, c-1]
                              MTX[1] = slab["DILFG", l, r-1, c]
                              MTX[2] = slab["DILFG", l, r-1, c+1]
                              MTX[3] = slab["DILFG", l, r, c-1]
                              MTX[5] = slab["DILFG", l, r, c+1]
                              MTX[6] = slab["DILFG", l, r+1, c-1]
                              MTX[7] = slab["DILFG", l, r+1, c]
                              MTX[8] = slab["DILFG", l, r+1, c+1]
                              if MTX[1] > 1 and MTX[3] > 1 and MTX[5] > 1 and MTX[7] > 1:  # 4 side test
                                 change = True
                              elif MTX[3] > 1 and MTX[1] > 1 and MTX[5] > 1:  # 3 side test-1 (bottom)
                                 change = MTX[0] > 1 and MTX[2] > 1
                              elif MTX[1] > 1 and MTX[3] > 1 and MTX[7] > 1:  # 3 side test-2 (left)
                                 change = MTX[0] > 1 and MTX[6] > 1
                              elif MTX[3] > 1 and MTX[7] > 1 and MTX[5] > 1:  # 3 side test-3 (top)
                                 change = MTX[6] > 1 and MTX[8] > 1
                              elif MTX[1] > 1 and MTX[5] > 1 and MTX[7] > 1:  # 3 side test-4 (right)
                                 change = MTX[2] > 1 and MTX[8] > 1
                              elif MTX[1] > 1 and MTX[7] > 1:                 # 2 side test-1 (opposite, vertical)
                                 change = not(MTX[3] < 2 and MTX[5] < 2) # horizontal line exception
                              elif MTX[3] > 1 and MTX[5] > 1:                 # 2 side test-2 (opposite, horizontal)
                                 change = not(MTX[1] < 2 and MTX[7] < 2) # vertical line exception
                              else:
                                 change = False
                              if change:
                                 slab["DILFG", l, r, c] = 3

               def OreTraverse_C():
               # 8-value traverse of the REVISED truncated slab for sulphide mill HG ORE diluted to WASTE
                  for r in xrange(1,rows-1):
                     for c in xrange(1,cols-1):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           # grab working copies of 3x3 area
                           # 6 7 8
                           # 3 4 5
                           # 0 1 2
                           MTX[4] = slab["DILFG", l, r, c]
                           if MTX[4] == 1:  # original ore blocks only
                              MTX[0] = slab["DILFG", l, r-1, c-1]
                              MTX[1] = slab["DILFG", l, r-1, c]
                              MTX[2] = slab["DILFG", l, r-1, c+1]
                              MTX[3] = slab["DILFG", l, r, c-1]
                              MTX[5] = slab["DILFG", l, r, c+1]
                              MTX[6] = slab["DILFG", l, r+1, c-1]
                              MTX[7] = slab["DILFG", l, r+1, c]
                              MTX[8] = slab["DILFG", l, r+1, c+1]
                              if MTX[1] > 1 and MTX[3] > 1 and MTX[5] > 1 and MTX[7] > 1:  # 4 side test
                                 change = True
                              elif MTX[3] > 1 and MTX[1] > 1 and MTX[5] > 1:  # 3 side test-1 (bottom)
                                 change = MTX[0] > 1 or MTX[2] > 1
                              elif MTX[1] > 1 and MTX[3] > 1 and MTX[7] > 1:  # 3 side test-2 (left)
                                 change = MTX[0] > 1 or MTX[6] > 1
                              elif MTX[3] > 1 and MTX[7] > 1 and MTX[5] > 1:  # 3 side test-3 (top)
                                 change = MTX[6] > 1 or MTX[8] > 1
                              elif MTX[1] > 1 and MTX[5] > 1 and MTX[7] > 1:  # 3 side test-4 (right)
                                 change = MTX[2] > 1 or MTX[8] > 1
                              elif MTX[1] > 1 and MTX[7] > 1:                 # 2 side test-1 (opposite, vertical)
                                 change = True
                              elif MTX[3] > 1 and MTX[5] > 1:                 # 2 side test-2 (opposite, horizontal)
                                 change = True
                              else:
                                 change = False
                              if change:
                                 slab["DILFG", l, r, c] = 3
               # -- end of subroutine definitions --

               OreTraverse_A()
               WasteTraverse_A()
               OreTraverse_B()
               WasteTraverse_B()
               OreTraverse_C()
               WasteTraverse_B()
               OreTraverse_C()
               OreTraverse_C()
               # == end of DILFG based dilution process ==

               # == DESTD modification based on result of kernel (DILFG) dilution (only on sulphide mill HG ORE) ==
               for r in xrange(1,rows-1):
                  for c in xrange(1,cols-1):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        if slab["DILFG", l, r, c] <= 0: # non-HG blocks (LG-N, W-PR, SP_OX ...) diluted to be sulphide mill feed (HG)
                           slab["DESTD", l, r, c] = HG
                        elif slab["DILFG", l, r, c] >= 3: # HG changed to Waste, default to LG class based on reactivity
                           WARDC = slab["WARDC", l, r, c]
                           if WARDC > 0:
                              slab["DESTD", l, r, c] = LG_N
                           else:
                              slab["DESTD", l, r, c] = LG_PR
               # == end of DESTD modification ==

               # == "salt & pepper" noise reduction for all destination codes, with exceptions in main body of code for HG and W_CV ==
               # -- DILFG assignment subroutine definitions (applied only to sulphide ore) --
               def HorseshoeBlocks(replacement,center,l,r,c):
                  slab["DESTD", l, r, c] = replacement
                  if center <= LG_N: # sulphide ore being replaced
                     if replacement <= LG_N: # sulphide ore replaced by sulphide ore
                        slab["DILFG", l, r, c] = 10
                     else:                         # sulphide ore replaced by waste
                        slab["DILFG", l, r, c] = 7
                  else: # waste being replaced
                     if replacement <= LG_N: # waste replaced by sulphide ore
                        slab["DILFG", l, r, c] = 4
                     else:                         # waste replaced by waste
                        slab["DILFG", l, r, c] = 13

               def ParallelBlocks(ro,co,replacement,center,l,r,c):
                  slab["DESTD", l, r, c] = replacement
                  slab["DESTD", l, r+ro, c+co] = replacement
                  if center <= LG_N: # sulphide ore being replaced
                     if replacement <= LG_N: # sulphide ore replaced by sulphide ore
                        slab["DILFG", l, r, c] = 11
                        slab["DILFG", l, r+ro, c+co] = 11
                     else:                         # sulphide ore replaced by waste
                        slab["DILFG", l, r, c] = 8
                        slab["DILFG", l, r+ro, c+co] = 8
                  else: # waste being replaced
                     if replacement <= LG_N: # waste replaced by sulphide ore
                        slab["DILFG", l, r, c] = 5
                        slab["DILFG", l, r+ro, c+co] = 5
                     else:                         # waste replaced by waste
                        slab["DILFG", l, r, c] = 14
                        slab["DILFG", l, r+ro, c+co] = 14

               def CornerBlocks(replacement,center,l,r,c):
                  slab["DESTD", l, r, c] = replacement
                  if center <= LG_N: # sulphide feed being replaced
                     if replacement <= LG_N: # sulphide ore replaced by sulphide ore
                        slab["DILFG", l, r, c] = 12
                     else:                         # sulphide ore replaced by waste
                        slab["DILFG", l, r, c] = 9
                  else: # waste being replaced
                     if replacement <= LG_N: # waste replaced by sulphide ore
                        slab["DILFG", l, r, c] = 6
                     else:                         # waste replaced by waste
                        slab["DILFG", l, r, c] = 15
               # -- end of subroutine definitions --

               for r in xrange(1,rows-1):
                  for c in xrange(1,cols-1):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        # grab working copies of 3x3 area
                        # 6 7 8
                        # 3 4 5
                        # 0 1 2
                        MTX[0] = slab["DESTD", l, r-1, c-1]
                        MTX[1] = slab["DESTD", l, r-1, c]
                        MTX[2] = slab["DESTD", l, r-1, c+1]
                        MTX[3] = slab["DESTD", l, r, c-1]
                        MTX[4] = slab["DESTD", l, r, c]
                        MTX[5] = slab["DESTD", l, r, c+1]
                        MTX[6] = slab["DESTD", l, r+1, c-1]
                        MTX[7] = slab["DESTD", l, r+1, c]
                        MTX[8] = slab["DESTD", l, r+1, c+1]

                        # run multiple block tests in a long if-then-else logic sequence

                        # 1) check for semi-surrounding 5 blocks on a side, i.e. horseshoe shape
                        if MTX[1]!=MTX[4] and ((MTX[1]==MTX[0] and MTX[1]==MTX[3] and MTX[1]==MTX[6] and MTX[1]==MTX[7]) or (MTX[1]==MTX[2] and MTX[1]==MTX[5] and MTX[1]==MTX[8] and MTX[1]==MTX[7])): # left or right
                           HorseshoeBlocks(MTX[1],MTX[4],l,r,c)
                        elif MTX[3]!=MTX[4] and ((MTX[3]==MTX[6] and MTX[3]==MTX[7] and MTX[3]==MTX[8] and MTX[3]==MTX[5]) or (MTX[3]==MTX[0] and MTX[3]==MTX[1] and MTX[3]==MTX[2] and MTX[3]==MTX[5])): # top or bottom
                           HorseshoeBlocks(MTX[3],MTX[4],l,r,c)
                        # 2) check for 2 similar block parallel lines; Cover or Mill Feed materials are exceptions in coding
                        elif MTX[4]==MTX[5] and MTX[7]==MTX[8] and MTX[1]==MTX[2] and MTX[7]!=MTX[4] and MTX[1]!=MTX[4]:  # above and below (horizontal)
                           if MTX[7]==MTX[1] or MTX[1]==W_CV or MTX[1]==HG:  # same 2 blocks above and below or if bottom 2 blocks are Cover or Mill Feed
                              ParallelBlocks(0,1,MTX[7],MTX[4],l,r,c)
                           elif MTX[7]==W_CV or MTX[7]==HG:  # top 2 blocks are Cover or Mill Feed
                              ParallelBlocks(0,1,MTX[1],MTX[4],l,r,c)
                           else:
                              ParallelBlocks(0,1,min(MTX[1],MTX[7]),MTX[4],l,r,c)
                        elif MTX[4]==MTX[1] and MTX[3]==MTX[0] and MTX[5]==MTX[2] and MTX[3]!=MTX[4] and MTX[5]!=MTX[4]:  # left and right (vertical)
                           if MTX[3]==MTX[5] or MTX[5]==W_CV or MTX[5]==HG:  # same 2 blocks left and right or if right 2 blocks are Cover or Mill Feed
                              ParallelBlocks(-1,0,MTX[3],MTX[4],l,r,c)
                           elif MTX[3]==W_CV or MTX[3]==HG:  # left 2 blocks are Cover or Mill Feed
                              ParallelBlocks(-1,0,MTX[5],MTX[4],l,r,c)
                           else:  # pick lowest code of either side
                              ParallelBlocks(-1,0,min(MTX[3],MTX[5]),MTX[4],l,r,c)
                        else:
                           # 3) check for contiguous 3 blocks in a corner; "Ore" and "Cover" materials are exceptions to coding
                           if MTX[4] > HG:  # do not change Mill Feed blocks if in 3 block set
                              if MTX[0]==MTX[3] and MTX[0]==MTX[1] and MTX[0]!=W_CV and MTX[0]!=HG:
                                 cornerCode = MTX[0]
                              elif MTX[2]==MTX[1] and MTX[2]==MTX[5] and MTX[2]!=W_CV and MTX[2]!=HG:
                                 cornerCode = MTX[2]
                              elif MTX[6]==MTX[3] and MTX[6]==MTX[7] and MTX[6]!=W_CV and MTX[6]!=HG:
                                 cornerCode = MTX[6]
                              elif MTX[8]==MTX[5] and MTX[8]==MTX[7] and MTX[8]!=W_CV and MTX[8]!=HG:
                                 cornerCode = MTX[8]
                              else:
                                 cornerCode = 0
                           HGc = MTX.count(HG)
                           LG_Nc = MTX.count(LG_N)
                           LG_PRc = MTX.count(LG_PR)
                           W_PRc = MTX.count(W_PR)
                           W_Nc = MTX.count(W_N)
                           W_CNc = MTX.count(W_CN)
                           W_CVc = MTX.count(W_CV)
                           SP_OXc = MTX.count(SP_OX)
                           SP_WXc = MTX.count(SP_WX)
                           # find most common code, but disregard Cover waste
                           if HGc >= max(LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                              mostCode = HG
                           elif LG_PRc >= max(HGc, LG_Nc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                              mostCode = LG_PR
                           elif LG_Nc >= max(HGc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                              mostCode = LG_N
                           elif W_PRc >= max(HGc, LG_Nc, LG_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                              mostCode = W_PR
                           elif W_Nc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_CNc, SP_OXc, SP_WXc):
                              mostCode = W_N
                           elif W_CNc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, SP_OXc, SP_WXc):
                              mostCode = W_CN
                           elif SP_OXc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_WXc):
                              mostCode = SP_OX
                           elif SP_WXc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc):
                              mostCode = SP_WX
                           else:
                              mostCode = 0
                           if mostCode > 0: # implement single or two block based change
                              if MTX[4] == LG_N:
                                 if LG_Nc <= 2 or (LG_Nc == 3 and (MTX[0] == LG_N or MTX[2] == LG_N or MTX[6] == LG_N or MTX[8] == LG_N)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == LG_PR:
                                 if LG_PRc <= 2 or (LG_PRc == 3 and (MTX[0] == LG_PR or MTX[2] == LG_PR or MTX[6] == LG_PR or MTX[8] == LG_PR)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == W_PR:
                                 if W_PRc <= 2 or (W_PRc == 3 and (MTX[0] == W_PR or MTX[2] == W_PR or MTX[6] == W_PR or MTX[8] == W_PR)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == W_N:
                                 if W_Nc <= 2 or (W_Nc == 3 and (MTX[0] == W_N or MTX[2] == W_N or MTX[6] == W_N or MTX[8] == W_N)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == W_CN:
                                 if W_CNc <= 2 or (W_CNc == 3 and (MTX[0] == W_CN or MTX[2] == W_CN or MTX[6] == W_CN or MTX[8] == W_CN)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == W_CV:
                                 if W_CVc <= 2 or (W_CVc == 3 and (MTX[0] == W_CV or MTX[2] == W_CV or MTX[6] == W_CV or MTX[8] == W_CV)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == SP_OX:
                                 if SP_OXc <= 2 or (SP_OXc == 3 and (MTX[0] == SP_OX or MTX[2] == SP_OX or MTX[6] == SP_OX or MTX[8] == SP_OX)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                              elif MTX[4] == SP_WX:
                                 if SP_WXc <= 2 or (SP_WXc == 3 and (MTX[0] == SP_WX or MTX[2] == SP_WX or MTX[6] == SP_WX or MTX[8] == SP_WX)):
                                    CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)

               # repeat test #3, Blocks in Corner, over changed DESTD codes; "Ore" and "Cover" materials are exceptions to coding
               for r in xrange(1,rows-1):
                  for c in xrange(1,cols-1):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        # grab working copies of 3x3 area
                        # 6 7 8
                        # 3 4 5
                        # 0 1 2
                        MTX[0] = slab["DESTD", l, r-1, c-1]
                        MTX[1] = slab["DESTD", l, r-1, c]
                        MTX[2] = slab["DESTD", l, r-1, c+1]
                        MTX[3] = slab["DESTD", l, r, c-1]
                        MTX[4] = slab["DESTD", l, r, c]
                        MTX[5] = slab["DESTD", l, r, c+1]
                        MTX[6] = slab["DESTD", l, r+1, c-1]
                        MTX[7] = slab["DESTD", l, r+1, c]
                        MTX[8] = slab["DESTD", l, r+1, c+1]
                        if MTX[4] > HG:  # do not change Mill Feed blocks if in 3 block set
                           if MTX[0]==MTX[3] and MTX[0]==MTX[1] and MTX[0]!=W_CV and MTX[0]!=HG:
                              cornerCode = MTX[0]
                           elif MTX[2]==MTX[1] and MTX[2]==MTX[5] and MTX[2]!=W_CV and MTX[2]!=HG:
                              cornerCode = MTX[2]
                           elif MTX[6]==MTX[3] and MTX[6]==MTX[7] and MTX[6]!=W_CV and MTX[6]!=HG:
                              cornerCode = MTX[6]
                           elif MTX[8]==MTX[5] and MTX[8]==MTX[7] and MTX[8]!=W_CV and MTX[8]!=HG:
                              cornerCode = MTX[8]
                           else:
                              cornerCode = 0
                        HGc = MTX.count(HG)
                        LG_Nc = MTX.count(LG_N)
                        LG_PRc = MTX.count(LG_PR)
                        W_PRc = MTX.count(W_PR)
                        W_Nc = MTX.count(W_N)
                        W_CNc = MTX.count(W_CN)
                        W_CVc = MTX.count(W_CV)
                        SP_OXc = MTX.count(SP_OX)
                        SP_WXc = MTX.count(SP_WX)
                        # find most common code, but disregard Cover waste
                        if HGc >= max(LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                           mostCode = HG
                        elif LG_PRc >= max(HGc, LG_Nc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                           mostCode = LG_PR
                        elif LG_Nc >= max(HGc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                           mostCode = LG_N
                        elif W_PRc >= max(HGc, LG_Nc, LG_PRc, W_Nc, W_CNc, SP_OXc, SP_WXc):
                           mostCode = W_PR
                        elif W_Nc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_CNc, SP_OXc, SP_WXc):
                           mostCode = W_N
                        elif W_CNc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, SP_OXc, SP_WXc):
                           mostCode = W_CN
                        elif SP_OXc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_WXc):
                           mostCode = SP_OX
                        elif SP_WXc >= max(HGc, LG_Nc, LG_PRc, W_PRc, W_Nc, W_CNc, SP_OXc):
                           mostCode = SP_WX
                        else:
                           mostCode = 0
                        if mostCode > 0: # implement single or two block based change
                           if MTX[4] == LG_N:
                              if LG_Nc <= 2 or (LG_Nc == 3 and (MTX[0] == LG_N or MTX[2] == LG_N or MTX[6] == LG_N or MTX[8] == LG_N)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == LG_PR:
                              if LG_PRc <= 2 or (LG_PRc == 3 and (MTX[0] == LG_PR or MTX[2] == LG_PR or MTX[6] == LG_PR or MTX[8] == LG_PR)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == W_PR:
                              if W_PRc <= 2 or (W_PRc == 3 and (MTX[0] == W_PR or MTX[2] == W_PR or MTX[6] == W_PR or MTX[8] == W_PR)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == W_N:
                              if W_Nc <= 2 or (W_Nc == 3 and (MTX[0] == W_N or MTX[2] == W_N or MTX[6] == W_N or MTX[8] == W_N)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == W_CN:
                              if W_CNc <= 2 or (W_CNc == 3 and (MTX[0] == W_CN or MTX[2] == W_CN or MTX[6] == W_CN or MTX[8] == W_CN)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == W_CV:
                              if W_CVc <= 2 or (W_CVc == 3 and (MTX[0] == W_CV or MTX[2] == W_CV or MTX[6] == W_CV or MTX[8] == W_CV)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == SP_OX:
                              if SP_OXc <= 2 or (SP_OXc == 3 and (MTX[0] == SP_OX or MTX[2] == SP_OX or MTX[6] == SP_OX or MTX[8] == SP_OX)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
                           elif MTX[4] == SP_WX:
                              if SP_WXc <= 2 or (SP_WXc == 3 and (MTX[0] == SP_WX or MTX[2] == SP_WX or MTX[6] == SP_WX or MTX[8] == SP_WX)):
                                 CornerBlocks(max(mostCode,cornerCode),MTX[4],l,r,c)
               # == end "salt & pepper" noise reduction ==

               # == DILFG reset (only on HG & LG_N) ==
               # reset DILFG if, after all of the above, it flip-flopped back and forth from what it originally was and is effectively now unchanged
               # NOTE: after this adjustment DILFG will still not exactly match R&R classification as dilution is of HG (only) using all RESCL, but REPORTABLE ores is based on MI&I only
               for r in xrange(rows):
                  for c in xrange(cols):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        DESTD = slab["DESTD", l, r, c]
                        DESTC = slab["DESTC", l, r, c]
                        if DESTD == DESTC:
                           if DESTD <= LG_N or DESTD >= SP_OX: # reportable sulphide, oxide, or weathered ores
                              slab["DILFG", l, r, c] = 1  # reset to unchanged REPORTABLE ores
                           else:
                              slab["DILFG", l, r, c] = 2  # unchanged as Waste
                        elif DESTD == LG_N: # exception for retagging LG sulphide ores considered Waste
                           DILFG = slab["DILFG", l, r, c]
                           if DILFG == 3:
                              slab["DILFG", l, r, c] = 0  # sulphide mill feed from Waste (LG)
               # == end DILFG reset ==

               # == DESTR assignment ==
               # sets DESTR based on DEST and, if DEST is a diluted value, resets DILFG for non-MI&I blocks so that DILFG and DESTR classifications will exactly match
               for r in xrange(rows):
                  for c in xrange(cols):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        DEST = slab[DESTname, l, r, c]
                        RESCL = slab["RESCL", l, r, c]
                        if DEST <= HG:  # HG sulphide mill feed
                           if RESCL <= 2:
                              slab["DESTR", l, r, c] = 1  # Measured & Indicated
                           elif RESCL <= 3:
                              slab["DESTR", l, r, c] = 2  # Inferred
                           else:  # HG sulphide mill feed reclassified to Waste
                              slab["DESTR", l, r, c] = 11
                              if DESTRdiluted:
                                 slab["DILFG", l, r, c] = 16  # dilution from R&R criteria
                        elif DEST <= LG_N: # Low Grade Non-reactive Stockpile
                           if RESCL <= 2:
                              slab["DESTR", l, r, c] = 3  # Measured & Indicated
                           elif RESCL <= 3:
                              slab["DESTR", l, r, c] = 4  # Inferred
                           else:  # LG sulphide mill stockpile reclassified to Waste
                              slab["DESTR", l, r, c] = 11
                              if DESTRdiluted:
                                 slab["DILFG", l, r, c] = 16  # dilution from R&R criteria
                        elif DEST <= LG_PR: # Low Grade Possibly Reactive (not stockpileable)
                           if RESCL <= 2:
                              slab["DESTR", l, r, c] = 5  # Measured & Indicated
                           elif RESCL <= 3:
                              slab["DESTR", l, r, c] = 6  # Inferred
                           else:  # LG possibly reactive reclassified to Waste
                              slab["DESTR", l, r, c] = 12
                              if DESTRdiluted:
                                 slab["DILFG", l, r, c] = 17  # dilution from R&R criteria
                        elif DEST >= SP_WX: # Weathered
                           if RESCL <= 2:
                              slab["DESTR", l, r, c] = 9  # Measured & Indicated
                           elif RESCL <= 3:
                              slab["DESTR", l, r, c] = 10  # Inferred
                           else:  # oxide mill feed reclassified to Waste
                              slab["DESTR", l, r, c] = 14
                              if DESTRdiluted:
                                 slab["DILFG", l, r, c] = 19  # dilution from R&R criteria
                        elif DEST >= SP_OX: # Oxide ore
                           if RESCL <= 2:
                              slab["DESTR", l, r, c] = 7  # Measured & Indicated
                           elif RESCL <= 3:
                              slab["DESTR", l, r, c] = 8  # Inferred
                           else:  # oxide mill feed reclassified to Waste
                              slab["DESTR", l, r, c] = 13
                              if DESTRdiluted:
                                 slab["DILFG", l, r, c] = 18  # dilution from R&R criteria
                        else:  # remainder are always waste classes for R&R
                           slab["DESTR", l, r, c] = 0
               # == end DESTR assignment ==

               # == DESTx reclassification ==
               # filter the DESTx code based on resource classification (RESCL)
               if filterDEST > 0:  # DESTx filtering is set
                  RESCLlimit = filterDEST + 1
                  # filterDEST=1 => RESCLlimit=2 => M&I => Ore in Inferred, Blue Sky, and Beyond-the-Sea reserve classes is considered Waste (typically for scheduling R&R production)
                  # filterDEST=2 => RESCLlimit=3 => MI&I => Ore only in Blue Sky and Beyond-the-Sea reserve classes is considered Waste (typically for reporting R&R)
                  for r in xrange(rows):
                     for c in xrange(cols):
                        if filter_by_period and not filter_by_period_ar:
                           PERLT = int(slab["PERLT", l, r, c])
                           run_calcs = PERLT < 1
                        else:
                           run_calcs = True
                        if run_calcs:
                           RESCL = slab["RESCL", l, r, c]
                           if RESCL > RESCLlimit: # only reclassify blocks of lower quality
                              if DESTRdiluted: # use DESTD and DESTC items
                                 DESTD = slab["DESTD", l, r, c]
                                 if DESTD <= LG_PR or DESTD >= SP_OX: # reclassify HG, LG-N, and LG-PR for sulphide mill and all oxide/weathered for secondary mill (whether exists or not)
                                    DESTC = slab["DESTC", l, r, c]
                                    if DESTC <= LG_PR or DESTC >= SP_OX:
                                       if WARDC <= 0: # 0 is possibly reactive
                                          slab["DESTD", l, r, c] = W_PR
                                       else:
                                          slab["DESTD", l, r, c] = W_N
                                    else:  # originally classified a waste class, so replace with original waste class
                                       slab["DESTD", l, r, c] = DESTC
                              else: # use DESTC item only
                                 DESTC = slab["DESTC", l, r, c]
                                 if DESTC <= LG_PR or DESTC >= SP_OX: # reclassify HG, LG-N, and LG-PR for sulphide mill and all oxide/weathered for secondary mill (whether exists or not)
                                    if WARDC <= 0: # 0 is possibly reactive
                                       slab["DESTC", l, r, c] = W_PR
                                    else:
                                       slab["DESTC", l, r, c] = W_N
               # == end DEST reclassification ==

               # == Concentrate calculations based on DESTx and redo of OPCST and VALS calculations for diluted values  ==
               for r in xrange(rows):
                  for c in xrange(cols):
                     if filter_by_period and not filter_by_period_ar:
                        PERLT = int(slab["PERLT", l, r, c])
                        run_calcs = PERLT < 1
                     else:
                        run_calcs = True
                     if run_calcs:
                        GEOL = slab["GEOL", l, r, c]
                        DEST = slab[DESTname, l, r, c]
                        if GEOL > Air: # not in air
                           # calculate concentrate and tailings tonnages for block
                           STZN = slab["STZN", l, r, c]
                           STPB = slab["STPB", l, r, c]
                           ODENM = slab["ODENM", l, r, c]
                           TonnesPerBlock = blockVolume*ODENM  # NOTE this is not adjusted by topo, will be taken care of by partials file
                           if DEST < SP_OX or DEST > SP_WX: # Sulfide (most destinations); includes MG
                              ZNREC = slab["ZNREC", l, r, c]
                              ZNGRD = slab["ZNGRD", l, r, c]
                              workZNCON = (STZN * ZNREC / ZNGRD)/100.0
                              PBREC = slab["PBREC", l, r, c]
                              PBGRD = slab["PBGRD", l, r, c]
                              workPBCON = (STPB * PBREC / PBGRD)/100.0
                           elif DEST >= SP_WX: # Weathered High Zn-Cu; MG selected above
                              ZNRWX = slab["ZNRWX", l, r, c]
                              ZNGWX = slab["ZNGWX", l, r, c]
                              workZNCON = (STZN * ZNRWX / ZNGWX)/100.0 # Zn basis for total Bulk Concentrate
                              workPBCON = 0.0
                           else: # DEST = SP_OX, i.e. Oxide High Pb-Ag
                              workZNCON = 0.0
                              PBROX = slab["PBROX", l, r, c]
                              PBGOX = slab["PBGOX", l, r, c]
                              workPBCON = (STPB * PBROX / PBGOX)/100.0
                           # concentrate and tailings tonnages
                           workZNCON = workZNCON * TonnesPerBlock
                           workPBCON = workPBCON * TonnesPerBlock
                           workTAILS = TonnesPerBlock - workZNCON - workPBCON

                           # rewrite OPCST and VALS for diluted blocks
                           if DESTRdiluted:
                              DESTD = slab["DESTD", l, r, c]
                              DESTC = slab["DESTC", l, r, c]
                              if DESTD != DESTC:
                                 MPT = slab["MPT", l, r, c] # min/t
                                 TPH = 60.0/MPT             # t/hr
                                 TPS = 1.0 / (MPT * 60.0)   # t/sec
                                 if (DESTC == LG_N and DESTD == HG) or (DESTC == HG and DESTD == LG_N):
                                    rewriteOPCST = True
                                    VALS = slab[VALSitem, l, r, c]
                                    OpCost = slab["OPCST", l, r, c]
                                    if DESTC == LG_N:
                                       OPCST_value = OpCost - rehandle_cost
                                       VALS_value = VALS + rehandle_cost * TPS
                                    else:  # DESTC == HG
                                       OPCST_value = OpCost + rehandle_cost
                                       VALS_value = VALS - rehandle_cost * TPS
                                 elif isQanaiyaq and (DESTC >= SP_OX and DESTD < SP_OX) or (DESTC < SP_OX and DESTD >= SP_OX):
                                    rewriteOPCST = True
                                    d = int(slab["DEP", l, r, c] - 1) # array index starts at 0
                                    SEsag = slab["SESAG", l, r, c]
                                    SEbm = slab["SEBM", l, r, c]
                                    if DESTD < SP_OX:
                                       AMR_TA = slab[VALTitem, l, r, c]
                                    elif DESTD >= SP_WX:
                                       AMR_TA = slab[VLTWitem, l, r, c]
                                    else: # == SP_OX
                                       AMR_TA = slab[VLTOitem, l, r, c]
                                    # calculate operating cost escalators and base operating cost ($/t)
                                    powerEsc = (SEsag + SEbm - averagePower) * powerCost  # grinding power cost escalator, (+) is increased cost
                                    throughputEsc = comminutionCost[d]*(averageTPH[d]/TPH - 1)  # throughput rate cost escalator, (+) is increased cost
                                    haulEsc = max((haulIncrBench[d] - b) * -haulIncrLU, (haulIncrBench[d] - b) * haulIncrLD)  # haulage cost adjustment above/below median bench (either direction an increase); (+) is increased cost; technically should not be included in $/s calc, but not large and easier to compute here than in MSSO
                                    OpCost_mill_noTails = haulEsc + (mill_cost[d] + powerEsc + throughputEsc) + indirect_cost/TPH
                                    # calculate 100% Tails operating cost and Mill cutoff ($/t)
                                    OpCost_mill_TA = OpCost_mill_noTails + tailsCostPerTonne # as 100% tailings
                                    MillCO_TA = OpCost_mill_TA + mine_ore_cost[d] - mine_waste_cost[d]
                                    # calculate $/s
                                    VALS_TA = (AMR_TA - MillCO_TA) * TPS  # $/sec for block for direct mill feed
                                    # set and rewrite VALS and OPCST items
                                    if DESTD == LG_N or DESTD >= SP_OX:  # set model values including rehandle cost
                                       OPCST_value = OpCost_mill_TA + rehandle_cost
                                       VALS_value = VALS_TA - rehandle_cost * TPS
                                    else:  # set model values default
                                       OPCST_value = OpCost_mill_TA
                                       VALS_value = VALS_TA
                                 else:
                                    rewriteOPCST = False
                                 # overwrite VALS and OPCST items if required
                                 if rewriteOPCST:
                                    slab[VALSitem, l, r, c] = VALS_value
                                    slab["OPCST", l, r, c] = OPCST_value

                           # assign MG blocks, if any
                           isMGO = slab["FLAG2", l, r, c] # used temporarily as boolean for MG possibility flag
                           if isMGO:
                              WARDC = slab["WARDC", l, r, c]
                              if WARDC > 0:
                                 MGO = MG_N
                              else:
                                 MGO = MG_PR
                              slab["DESTC", l, r, c] = MGO
                              if DESTRdiluted:
                                 DESTD = slab["DESTD", l, r, c]
                                 if DESTD == HG:
                                    slab["DESTD", l, r, c] = MGO
                                    DEST = MGO
                              else:
                                 slab["DESTD", l, r, c] = MGO
                                 DEST = MGO
                        else: # in Air
                           workZNCON = 0.0
                           workPBCON = 0.0
                           workTAILS = 0.0

                        # write revised values
                        slab["ZNCON", l, r, c] = workZNCON
                        slab["PBCON", l, r, c] = workPBCON
                        slab["TAILS", l, r, c] = workTAILS
                        # == end Concentrate calculations ==

                        # == Blastability Class ==
                        d = int(slab["DEP", l, r, c] - 1) # array index starts at 0
                        if GEOL in Construction[d]:
                           BAC = 1
                        elif GEOL in Black_Shale[d]:
                           BAC = 2
                        elif GEOL in Baritic[d]:
                           if DEST >= W_PR and DEST <= SP_WX: # waste
                              BAC = 3
                           else: # ore
                              BAC = 4
                        elif GEOL in Non_Baritic[d]:
                           STFE = slab["STFE", l, r, c]
                           if DEST <= LG_PR or DEST >= MG_N: # ore
                              if STFE <= 20: # lower iron
                                 BAC = 5
                              else: # higher iron
                                 BAC = 6
                           else: # waste
                              BAC = 7
                        else:
                           BAC = 0 # not otherwise classified
                        slab["BAC", l, r, c] = BAC
                        # == end Blastability Class ==

                        # == ORCT4 filtering based on DEST ==
                        if GEOL > Air: # not in the air
                           if DEST >= LG_N: # all classes except Direct Mill Feed
                              ORCT4 = DEST + 18  # set all non-mill feed destinations to DEST code + 18, e.g. LG_N=2 becomes ORCT4=20, etc
                           else: # DEST = HG
                              ORCT2 = slab["ORCT2", l, r, c]
                              if ORCT2 >= 5 and ORCT2 != 8: # Shales
                                 ORCT4 = 0
                              elif STZN < 15: # low zinc grade
                                 if ORCT2 <= 1: # Exhalite
                                    ORCT4 = 1
                                 elif ORCT2 <= 2: # Weathered
                                    ORCT4 = 4
                                 elif ORCT2 <= 3: # Baritic
                                    ORCT4 = 7
                                 elif ORCT2 <= 4: # Iron-rich
                                    ORCT4 = 10
                                 else: # ORCT2 = 8, # Veined
                                    ORCT4 = 13
                              elif STZN >= 25: # high zinc grade
                                 if ORCT2 <= 1: # Exhalite
                                    ORCT4 = 3
                                 elif ORCT2 <= 2: # Weathered
                                    ORCT4 = 6
                                 elif ORCT2 <= 3: # Baritic
                                    ORCT4 = 9
                                 elif ORCT2 <= 4: # Iron-rich
                                    ORCT4 = 12
                                 else: # ORCT2 = 8, # Veined
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
                                 else: # ORCT2 = 8, # Veined
                                    ORCT4 = 14
                        else: # in air
                           ORCT4 = model.UNDEFINED
                        slab["ORCT4", l, r, c] = ORCT4
                        # == end ORCT4 filtering ==

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
