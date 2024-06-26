#==============================================================================
# AMR economics calculation
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
from grail import rtv

#==============================================================================
# Version Information
#==============================================================================

PROC_TITLE = "AMR/NSR Calculation - ver 5.23.2 - Feb 10, 2023"

# QTR 2, 2014 - v3: updated for May 2014 metal prices
# Sept 26, 2014 - v3a: added loop for Qanaiyaq oxide ore processing VALTO
# Dec 20, 2014 - v3b: added output of oxide ore processing VALTO for all models
# Apr 4, 2015 - v3c: updated for Feb 2015 metal prices and revised smelter terms
# Apr 27, 2015 - v3d: updated for revised shipping costs
# May 8, 2015 - v4: removed bench elevation escalator (put in DEST) and 0 value clipping from NSR calc; updated escalators for grinding energy and throughput for mid-2015
# July 17, 2015 - v4a: added bench elevation escalator back in for R&R Breakeven cost calculation
# Nov 20, 2015 - v5: modified to use MPT (minutes-per-tonne) instead of TPH (tonnes-per-hour)
# Mar 24, 2016 - v5a: added GEOL check for Air; removed escalation if neither Pb nor Zn conc produced; renamed Non-Sulphide items to Oxide
# Apr 4, 2016 - v5b: updated costs for mid-2016 (based on 2016 O-LOM c/o); added text log file for script execution
# May 27, 2016 - v5.03 (5c): updated costs for mid-2016 (based on 2017 S-LOM c/o)
# July 2, 2016 - v5.03_5300: changed comminution cost and average TPH for 2017 LOM-O schedule
# Oct 28, 2016 - v5.04VIP (03.01_5300): moved Date-Time stamp to top of text output and added user name; keep negative values of VALT to ensure "waste diluted to mill feed" gets Power, Throughput, and Haulage escalators;
# Mar 4, 2017 - v5.04.01VIP: updated for Feb 2017 Long Term metal prices; renamed SPNRG to SESAG
# Mar 31, 2017 - v5.05VIP: updated power and comminution costs and average TPH rates; updated & changed freight and smelter costs and calculations; added concentrate dewatering, business interruption insurance,
#                          and NW Arctic Borough Tax to concentrate NSR calculation
# July 1, 2017 - v5.05.01VIP: added computation only for years < 1 (i.e. UNDEF or 0); removed Debug coding
# Jan 23, 2018 - v5.10: converted to use Ag grades in, instead of recoveries to, concentrates and renamed model items to AGGZN, AGGPB, and AGGOX; changed BII first to be applied against gross conc revenue (contained metal)
#                       instead of gross conc payment (paid metal) then again to be applied against net conc revenue (Payable less Treatment, not Freight or Sales);
#                       changed NSR, "Net Smelter Return", label to AMR, "At Mine Revenue", label where applicable; re-organized AMR calculation to be a function and added a function to compute bulk conc AMR;
#                       modified haulage increment to apply both below and above index bench; adjusted metal prices and TC to 2018 Guidance; adjusted costs to EcM_20180122;
# Feb 6, 2018 - v5.11: revised freight costs to Jan 2018 forecast; updated power escalator in throughput calculation;
# [June 2, 2018]       added "Failed!" to output text file if run incomplete;
# [Oct 17, 2018]       replaced YEAR with PERLT as MSSO periods of variable size;
# Dec 30, 2018 - v5.20: relocated throughput and power escalator programming to DEST script (as these are site costs); changed GEOL code for Air from 50 to 0;
# Feb 15, 2019 - v5.20.1: updated costs for LOM2020;
# Apr 4, 2019 - v5.20.2: revised costs for LOM2020 based on newer (March 15) version of economic spreadsheet;
# Apr 17, 2019 - v5.20.3: revised costs for LOM2020 based on reversion back to 4.5% rate for Severance tax years and Sustaining Capital reorganization in Econ workbook (mine, mill, port)
# May 18, 2019 - v5.20.4: revised costs and NWABT for 5-YR Plan based on 'EcM20190517_12-7.5p12_2.10rem_20190507.xlsx' parameters
# Feb 17, 2020 - v5.21: removed Period spinner (obsolete, for pre-VIP2); updated costs for LOM2021 based on 'EcM LOM 2021 - 20200217.xlsx' R&R parameters;
# Apr 24, 2020 - v5.22: changed selling cost to new (flat rate) contract terms; updated costs for 2021LOM-O based on 'EcM LOM 2021 - 20200424.xlsx' R&R parameters;
# July 19, 2020 - v5.22.1: updated costs for 2021-5YR based on 'EcM LOM 2021 - 20200719.xlsx' R&R parameters;
# Feb 28, 2021 - v5.23.0: updated costs for 2022 LOM based on 'EcM LOM 2022 - 20210228.xlsx' R&R parameters;
# Jan 19, 2022-v5.23.1: updated the cost for the 2023 LOM based on the price guidance on '2023 LOM EcM 20220119_LG_inputs'
# Feb 15, 2022- v5.23.1: Checked few more parameters, for ZnPayPb, using the 50% shipping, and 50% recovery
# Feb 9, 2023- v5.23.2: Updated the numbers with new costs from the 2024 LOM Economic Model 01182023.xlsx, which is the Input Assumptions and Economic Model Folder, Updated on Feb 9, 2023
# July 3, 2023- v5.23.3 Updated the costs number for the 5YBP, 2023 



##### future change for new geology models coding -> # XXX xx, 2020 - v5.XX xxx: changed GEOL to GEOL1 (sulfide majority code)

#==============================================================================
# Constants
#==============================================================================

# items to get from model
itemlist = ["PERLT","GEOL","STZN","STPB","AGM","ZNREC","PBREC","AGGZN","AGGPB","ZNGRD","PBGRD"]
itemlistQanAdd = ["AGGOX","PBROX","PBGOX","AGGWX","ZNGWX","PBGWX","ZNRWX","PBRWX"]

# geology codes
Air = 0

# metal prices
baseZnPrice, basePbPrice, baseAgPrice = 120, 90, 2000 # c/lb, c/lb, c/tr oz # Checked from Guidance for LOM 2024

# smelter terms
##ZnTcBase, ZnTcBasisN3, ZnTcBasisN2, ZnTcBasisN1, ZnTcBasis, ZnTcBasisP1, ZnTcBasisP2, ZnTcBasisP3, ZnTcBasisP4 = 251.20, 1500.0, 2000.0, 2100.0, 2300.0, 2500.0, 3000.0, 3500.0, 3750.0  # $/t
##ZnBelowBasisN3, ZnBelowBasisN2, ZnBelowBasisN1, ZnBelowBasis, ZnAboveBasis, ZnAboveBasisP1, ZnAboveBasisP2, ZnAboveBasisP3, ZnAboveBasisP4  = -0.0165, -0.0343, -0.0619, -0.0623, 0.0705, 0.0617, 0.0469, 0.0365, 0.0304 # $/$
ZnTcBase, ZnTcBasis = 260.0, 0.0  # $/t # Checked from Guidance and Econ Model tab Price Assumption
ZnBelowBasis, ZnAboveBasis  = 0.0, 0.0  # $/$
GePayment = (0.08-0.065)*0.20*((1000.0/0.69405)-120) # $/t, equation is: (grade - deduct)* pay *(( [GeO2 price] /[GeO2 conversion]) - refine); NOTE "pay" is 40%, but only from Trail which is 50% ship from LOM average, so effective pay is 20%
SiPenalty = (0.0400-0.0325)*1.50  # $/t, equation is: (grade - deduct)* charge; based on ~4% expected through LOM (5 year {2013-2018} average is 3.84%)
ZnFlatPenalty = 0.00 # $/t
ZnPayZn, ZnDeductZn = 0.85, 0.08 # %, %
ZnPayAg, ZnDeductAg, ZnRefineAg = 0.70, 3.000*31.10348, 0.0 # %, g/t, $/g
ZnPayPb = 0.0 # %
PbTcBase, PbTcBasis = 150.0, 2000.0 # $/t, $/t # Checked from Guidance and Econ Model tab Price Assumption
PbBelowBasis, PbAboveBasis = 0.0, 0.0 # $/$, $/$
PbFlatPenalty = 0.00 # $/t
PbPayPb, PbDeductPb = 0.95, 0.03 # %, %
PbPayAg, PbDeductAg, PbRefineAg = 0.95, 42.210, 0.782/31.10348 # %, g/t, $/g
PbPayZn = 0.098 # Pay is only 50%, since the other 50% smelter does not pay for the the Zn in Pb Conc
BkPayAg, BkDeductAg = 0.70, 3.000*31.10348 # %, g/t
# ZNGPB = 0.111 # Zinc Grade in Pb Conc for the Year (11.1 % for LOM 2023, Converted to number, Value obtained from Simon Yu via Email)

# concentrate oxidation reduction (no oxidation reduction with Bulk conc as unknown)
ZnCGreduction = 0.0075 # %, This value is available in NSR spreadsheet 
PbCGreduction = 0.0 # %

# shipping costs
ZnFreight = 101.47 # $/dmt # $/t section C88
PbFreight = 103.63 # $/dmt # $/t section C 89
BkFreight = (ZnFreight + PbFreight)/2 # $/dmt

# other concentrate costs ##### These values comes from the $/t sheet of the LOM Excel file
portsite = 23.71  # $/t concentrate (ops, road maintenance, catering) # $/t C 87
dewatering = 10.11 # $/t concentrate (labor, maintenance, & power) # $/t C86
BII = 0.0031 # business interruption insurance, against gross (vs. payable) concentrate revenue # G&A F7, remains unchanged confirmed by Andrew
NWABTeff = 0.0271 # NW Arctic Borough Tax: schedule weighted average of# i) 4.50% Severance Tax and ii) depreciation based PILT+VIF charge. This is against gross concentrate revenue less treatment and freight charges (sell expense not deducted). $/t tab C 105

#selling expense
ZnSell, PbSell = 2.79, 2.97 # $/dmt concentrate $/t P7
BkSell = (ZnSell + PbSell)/2 # $/dmt concentrate $/t Q7

#==============================================================================
# Panel 1
#==============================================================================

file15 = StringRTV(name="file15")

pickPriceZn = IntegerRTV(name="pickPriceZn", value=baseZnPrice)
pickPricePb = IntegerRTV(name="pickPricePb", value=basePbPrice)
pickPriceAg = IntegerRTV(name="pickPriceAg", value=baseAgPrice)

NUM_ITEMS = 1
ModelItems = [(StringRTV(name="item1" + str(i))) for i in range(NUM_ITEMS)]
ModelLabels = [("$/t var:") for i in range(NUM_ITEMS)]

# top = gtools.splitframe(root)

class DefineModelFile(GPanel):

   def makewidgets(self):
      self.makeFilePickers()
      self.makeItems()
      objsignal.listen(file15, "onChange()", self, self.onFile15Change)
      self.onFile15Change(file15)
      self.makePriceSpinner1()
      self.makePriceSpinner2()
      self.makePriceSpinner3()
      # self.makeCommentBox()


   def makeFilePickers(self):
      grp = GGroup(self, text="Choose model file")
      grp.pack(anchor=NW, pady=2, padx=2, ipadx = 2, ipady=2)
      item15 = cmpsys.getpcf().filelistbytype(15)
      cbs = GComboBox(grp.interior(), items=item15, rtv=file15)
      lbls = GLabel(grp.interior(), text="Name of 3D block model:")
      gtools.stdwidgetcolumns([lbls], [cbs])
      self.remember([cbs])

   def makeItems(self):
      grp = GGroup(self, text="Store VALT in item")
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

   def makePriceSpinner1(self):
      price = 1
      grp = GGroup(self, text="Zn price (cents/lb)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      pricespin = GSpinner(grp.interior(), min = 10, max = 500, rtv = pickPriceZn)
      pricespin.pack(side='top', anchor=W, padx=20, pady=2)
      self.remember([pricespin])

   def makePriceSpinner2(self):
      price = 2
      grp = GGroup(self, text="Pb price (cents/lb)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      pricespin = GSpinner(grp.interior(), min = 10, max = 500, rtv = pickPricePb)
      pricespin.pack(side='top', anchor=W, padx=20, pady=2)
      self.remember([pricespin])

   def makePriceSpinner3(self):
      price = 3
      grp = GGroup(self, text="Ag price (cents/ozt)")
      grp.pack(side='top', anchor=W, pady=2, padx=2)
      pricespin = GSpinner(grp.interior(), min = 100, max = 5000, rtv = pickPriceAg)
      pricespin.pack(side='top', anchor=W, padx=25, pady=2)
      self.remember([pricespin])

   # def makeCommentBox(self):
   #    # grp = GGroup(self, text="Comment")
   #    # grp.pack(side='top', anchor=W, pady=2, padx=2)
   #    var = rtv.StringRTV(value='This is a test!', name="__gtextentry test")
   #    te = GTextEntry(top, width= 35, text = 'comment here', rtv=var)
   #    te.pack(expand=1, fill=Tkinter.X, anchor='nw')
   #    self.remember([te])


              #==============================================================================
# Folder Layout
#==============================================================================

PANEL1 = "Model File Information"
PROC_FOLDERS = GFolder("Model Operations", [GItem(PANEL1, DefineModelFile)])

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

   # replacement for col, row, level spinners
   pcf = cmpsys.getpcf()
   minColumn, minRow, minLevel = 1, 1, 1
   maxColumn, maxRow, maxLevel = pcf.nx(), pcf.ny(), pcf.nz()
##   minColumn, minRow, minLevel = 62, 113, 14  # for debuggging
##   maxColumn, maxRow, maxLevel = 62, 113, 14  # for debuggging

   # get AMR storage variable name from panel and append to "itemlist", including placeholders for Qanaiyaq variables
   for item in ModelItems:
      if item.get() != '':
         # get sulphide item, VALTx, and append
         VALTitem = item.get()
         itemlist.append(VALTitem)
         # turn VALTx into VLTOx and append
         VLTOitem = VALTitem.replace("ALT","LTO")
         itemlist.append(VLTOitem)
         # turn VALTx into VLTWx and append
         VLTWitem = VALTitem.replace("ALT","LTW")
         itemlist.append(VLTWitem)
         break

   # check if path to a Qanaiyaq model
   isQanaiyaq = "QAN" in pcfpath or "qan" in pcfpath or "Qan" in pcfpath
   if isQanaiyaq:
      msgText = "\n  Qanaiyaq model "+file15.get()+" in "+projdir
      print msgText
      PyLogFile.write(msgText)
      msgText = "\n  AMR calculated for sulphide, oxide Pb-Ag, and weathered Zn-Cu floatation\n"
      print msgText
      PyLogFile.write(msgText)
      # add oxide and weathered metallurgy parameters to model item list
      itemlist.extend(itemlistQanAdd)
   else:
      msgText = "\n  Aqqaluk model "+file15.get()+" in "+projdir
      print msgText
      PyLogFile.write(msgText)
      msgText = "\n  AMR calculated only for sulphide floatation (no oxide Pb-Ag or weathered Zn-Cu in Aqqaluk)\n"
      print msgText
      PyLogFile.write(msgText)

   # get prices from panel variables (note they are in cents not dollars)
   ZnPrice = pickPriceZn.get() / 100.00
   PbPrice = pickPricePb.get() / 100.00
   AgPrice = pickPriceAg.get() / 100.00

   # calculations which are not required to be repeated in the loop
   ZnPricet = ZnPrice*2204.62 # $/t
   PbPricet = PbPrice*2204.62 # $/t
   AgPriceg = AgPrice/31.10348 # $/g
   ZnConcPayPb = PbPricet * ZnPayPb  # $/t
   PbConcPayZn = ZnPricet * PbPayZn  # $/t

   # zinc treatment charge calc
   if ZnPricet > ZnTcBasis:
      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
   else:
      ZnTc = ZnTcBase + (ZnTcBasis-ZnPricet)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty

## complex Price Participation, may be reused one day
##
##   if ZnPricet > ZnTcBasisP4:
##      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasisP4)*ZnAboveBasisP4 + (ZnTcBasisP4-ZnTcBasisP3)*ZnAboveBasisP3 + (ZnTcBasisP3-ZnTcBasisP2)*ZnAboveBasisP2 + (ZnTcBasisP2-ZnTcBasisP1)*ZnAboveBasisP1 + (ZnTcBasisP1-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisP3:
##      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasisP3)*ZnAboveBasisP3 + (ZnTcBasisP3-ZnTcBasisP2)*ZnAboveBasisP2 + (ZnTcBasisP2-ZnTcBasisP1)*ZnAboveBasisP1 + (ZnTcBasisP1-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisP2:
##      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasisP2)*ZnAboveBasisP2 + (ZnTcBasisP2-ZnTcBasisP1)*ZnAboveBasisP1 + (ZnTcBasisP1-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisP1:
##      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasisP1)*ZnAboveBasisP1 + (ZnTcBasisP1-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasis:
##      ZnTc = ZnTcBase + (ZnPricet-ZnTcBasis)*ZnAboveBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisN1: # less than Base
##      ZnTc = ZnTcBase + (ZnTcBasis-ZnPricet)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisN2:
##      ZnTc = ZnTcBase + (ZnTcBasisN1-ZnPricet)*ZnBelowBasisN1 + (ZnTcBasis-ZnTcBasisN1)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty
##   elif ZnPricet > ZnTcBasisN3:
##      ZnTc = ZnTcBase + (ZnTcBasisN2-ZnPricet)*ZnBelowBasisN2 + (ZnTcBasisN1-ZnTcBasisN2)*ZnBelowBasisN1 + (ZnTcBasis-ZnTcBasisN1)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty
##   else: # < ZnTcBasisN3
##      ZnTc = ZnTcBase + (ZnTcBasisN3-ZnPricet)*ZnBelowBasisN3 + (ZnTcBasisN2-ZnTcBasisN3)*ZnBelowBasisN2 + (ZnTcBasisN1-ZnTcBasisN2)*ZnBelowBasisN1 + (ZnTcBasis-ZnTcBasisN1)*ZnBelowBasis - GePayment + SiPenalty + ZnFlatPenalty

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

   # describe case
   msgText = "  Metal prices of $%3.2f/lb Zn, $%3.2f/lb Pb, and $%4.2f/ozt Ag\n" % (ZnPrice, PbPrice, AgPrice)
   print msgText
   PyLogFile.write(msgText)
   if isQanaiyaq:
      msgText = "  Sulphide, Oxide, and Weathered $/t values stored in "+VALTitem+", "+VLTOitem+" and "+VLTWitem+"\n"
   else:
      msgText = "  Sulphide $/t value stored in "+VALTitem+"\n"
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
            # traverse the slab, get values, calculate, and set the new value
            for r in xrange(rows):
               for c in xrange(cols):
                  GEOL = slab["GEOL", l, r, c]
                  if GEOL == Air: # geology is above topography, so no AMR can be calculated
                     VALTs = 0.0
                     VALTox = 0.0
                     VALTwx = 0.0
                  else: # geology is not above topography, so calculate AMR
                     # grab copies and ensure they are defined
                     STZN = slab["STZN", l, r, c]
                     if model.isdefined(STZN)<1:
                        STZN = 0.0
                     STPB = slab["STPB", l, r, c]
                     if model.isdefined(STPB)<1:
                        STPB = 0.0
                     AGM = slab["AGM", l, r, c]
                     if model.isdefined(AGM)<1:
                        AGM = 0.0
                     ZNREC = slab["ZNREC", l, r, c] #### Zn Recovery
                     PBREC = slab["PBREC", l, r, c] #### Pb Recovery
                     AGGZN = slab["AGGZN", l, r, c] #### Ag Grade in Zn Conc
                     AGGPB = slab["AGGPB", l, r, c] #### AG Grade in Pb Conc
                     ZNGRD = slab["ZNGRD", l, r, c] #### Zn Grade in Zn Conc
                     PBGRD = slab["PBGRD", l, r, c] #### Pb Grade in Pb Conc
                     if isQanaiyaq:
                        # get oxide float metallurgical parameters
                        AGGOX = slab["AGGOX", l, r, c] #### Ag Grade in Pb Oxide Conc
                        PBGOX = slab["PBGOX", l, r, c] #### Pb grade in oxide ore Conc
                        PBROX = slab["PBROX", l, r, c] #### Pb recovery to Pb in oxide ore Conc
                        # get weathered float metallurgical parameters
                        AGGWX = slab["AGGWX", l, r, c] #### Ag grade in weathered ore Bulk conc
                        ZNGWX = slab["ZNGWX", l, r, c] #### Zn Grade in Weathered Ore Bulk
                        PBGWX = slab["PBGWX", l, r, c] #### Pb Grade in Weathered Ore Bulk
                        ZNRWX = slab["ZNRWX", l, r, c] #### Zn recovery to weathered ore Bulk conc

                        PBRWX = slab["PBRWX", l, r, c] #### Pb recovery to weathered ore Bulk conc

                     # start NSR/AMR calculations
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
                           buroughTax = NWABTeff * (grossConcPay - totalTc - Freight)
                           netConcPay = grossConcPay - totalTc - Freight - Selling - busIntrptIns - buroughTax - dewateringPS - portsite
                           AMR = netConcPay * ConcShipped
###################################################
###  DEBUGGING code for NSR model
##                              ConcProduced = (Gfeed*Rconc)/100.0 / Gconc
##                              grossConcRev = Pricet * CGnet + AgPriceg * GconcAgNet  # calculation was changed again for BII in EcM in mid-Jan 2018
##
##                              print "ConcShipped:%7.4f  AginConcPay:%8.3f  totalTc:%8.3f  ConcPay:%9.3f  GrossConcPay:%9.3f  Selling:%6.3f   Freight:%6.3f" % (ConcShipped,AginConcPay/31.10348,totalTc,ConcPay,grossConcPay,Selling,Freight)
##                              print "ConcProduced:%7.4f  dewater:%6.3f  GrossConcRev:%9.3f  busIntIns:%6.3f  BuroughTax:%7.3f  netConcPay:%8.3f  AMR:%8.3f" % (ConcProduced,dewateringPS,grossConcRev,busIntrptIns,buroughTax,netConcPay,AMR)
##                              print "row:%3d  col:%3d  bench:%3d\n" % ((r+minRow),(c+minColumn),minLevel)
###################################################
                        else:
                           AMR = 0.0
                        return AMR;
                     # end of single metal AMR calculation function
                     #=====================================
                     # Function to calculate AMR for a bulk concentrate ($/tonne mill feed)
                     def AMR_bulk():
                        ZnCGnet = ZNGWX/100.0 ####ZNGWX ZN Grade in weathered ore Bulk Conc
                        PbCGnet = PBGWX/100.0 ##### Pb Grade in weathered ore Bulk Conc
                        if ZnCGnet > 0:
                           ConcShipped = (STZN*ZNRWX)/10000.0 / ZnCGnet
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
###################################################
###  DEBUGGING code for NSR model
##                              ConcProduced = (STZN*ZNRWX)/100.0 / ZNGWX
##                              grossConcRev = ZnPricet * ZnCGnet + PbPricet * PbCGnet + AgPriceg * GconcAgNet   # calculation was changed again for BII in EcM in mid-Jan 2018
##
##                              print "ConcShipped:%7.4f  AginConcPay:%8.3f  totalTc:%8.3f  ConcPay:%9.3f  GrossConcPay:%9.3f  Selling:%6.3f   Freight:%6.3f" % (ConcShipped,AginConcPay/31.10348,totalTc,ConcPay,grossConcPay,BkSell,BkFreight)
##                              print "ConcProduced:%7.4f  dewater:%6.3f  GrossConcRev:%9.3f  busIntIns:%6.3f  BuroughTax:%7.3f  netConcPay:%8.3f  AMR:%8.3f" % (ConcProduced,dewateringPS,grossConcRev,busIntrptIns,buroughTax,netConcPay,AMR)
##                              print "row:%3d  col:%3d  bench:%3d\n" % ((r+minRow),(c+minColumn),minLevel)
###################################################
                        else:
                           AMR = 0.0
                        return AMR;
                     # end of bulk concentrate AMR calculation function
                     #=====================================

                     # calculate Sulphide float AMR for all deposits
                     VALTzn = AMR_single('ZN',STZN,ZNGRD,ZNREC,AGGZN,ZnCGreduction,ZnPricet,ZnPayZn,ZnDeductZn,ZnConcPayPb,ZnTc,ZnDeductAg,ZnPayAg,ZnRefineAg,ZnFreight,ZnSell)
                     VALTpb = AMR_single('PB',STPB,PBGRD,PBREC,AGGPB,PbCGreduction,PbPricet,PbPayPb,PbDeductPb,PbConcPayZn,PbTc,PbDeductAg,PbPayAg,PbRefineAg,PbFreight,PbSell)
                     VALTs = VALTzn + VALTpb # do not set VALTs to 0 if no concentrate value, keep negative or positive values of VALTs
                     # if Qanaiyaq, also calculate Oxide and Weathered float AMR
                     if isQanaiyaq:
                        # calculate Oxide float AMR (Pb conc)
                        VALTox = AMR_single('PB',STPB,PBGOX,PBROX,AGGOX,PbCGreduction,PbPricet,PbPayPb,PbDeductPb,0.0,PbTc,PbDeductAg,PbPayAg,PbRefineAg,PbFreight,PbSell)
                        # calculate Weathered float AMR (bulk conc)
                        VALTwx = AMR_bulk()
                     else:
                        VALTox = 0.0
                        VALTwx = 0.0
###################################################
###  DEBUGGING code for NSR model
##                     print "VALTs:%9.3f\n" % (VALTs)
##                     if isQanaiyaq:
##                        print "VALTox:%9.3f  VALTwx:%9.3f\n" % (VALTox,VALTwx)
###################################################
                  # write values
                  slab[VALTitem, l, r, c] = VALTs
                  slab[VLTOitem, l, r, c] = VALTox
                  slab[VLTWitem, l, r, c] = VALTwx
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
