
# parsetab.py
# This file is automatically generated. Do not edit.
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'rightEQVIrightIMPLleftANDORleftNOTleftPOSSleftNECEID AND OR NOT EQVI IMPL PTRUE PFALSE LPAREN RPAREN SEMICOLON COMMA LBRACE RBRACE POSS NECE MODEL ENDspec : kripkemodel formulasformulas : formula SEMICOLONformulas : formulas formula SEMICOLONkripkemodel : MODEL worldlist END MODELworldlist : worldworldlist : worldlist worldworld : ID LBRACE stringlist RBRACE stringlist SEMICOLONstringlist :stringlist : stringlist1stringlist1 : IDstringlist1 : stringlist1 COMMA IDformula : formula AND formula\n                | formula OR formula\n                | formula IMPL formula\n                | formula EQVI formulaformula : NOT formulaformula : POSS formulaformula : NECE formulaformula : PTRUEformula : PFALSEformula : IDformula : LPAREN formula RPAREN'
    
_lr_action_items = {'MODEL':([0,26,],[3,35,]),'$end':([1,4,17,29,],[0,-1,-2,-3,]),'NOT':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[6,6,6,6,6,6,-2,6,6,6,6,-3,-4,]),'POSS':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[7,7,7,7,7,7,-2,7,7,7,7,-3,-4,]),'NECE':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[8,8,8,8,8,8,-2,8,8,8,8,-3,-4,]),'PTRUE':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[9,9,9,9,9,9,-2,9,9,9,9,-3,-4,]),'PFALSE':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[10,10,10,10,10,10,-2,10,10,10,10,-3,-4,]),'ID':([2,3,4,6,7,8,12,13,14,17,18,19,20,21,27,28,29,35,39,40,43,],[11,15,11,11,11,11,11,15,-5,-2,11,11,11,11,-6,36,-3,-4,36,42,-7,]),'LPAREN':([2,4,6,7,8,12,17,18,19,20,21,29,35,],[12,12,12,12,12,12,-2,12,12,12,12,-3,-4,]),'SEMICOLON':([5,9,10,11,16,22,23,24,30,31,32,33,34,36,38,39,41,42,],[17,-19,-20,-21,29,-16,-17,-18,-12,-13,-14,-15,-22,-10,-9,-8,43,-11,]),'AND':([5,9,10,11,16,22,23,24,25,30,31,32,33,34,],[18,-19,-20,-21,18,-16,-17,-18,18,-12,-13,18,18,-22,]),'OR':([5,9,10,11,16,22,23,24,25,30,31,32,33,34,],[19,-19,-20,-21,19,-16,-17,-18,19,-12,-13,19,19,-22,]),'IMPL':([5,9,10,11,16,22,23,24,25,30,31,32,33,34,],[20,-19,-20,-21,20,-16,-17,-18,20,-12,-13,20,20,-22,]),'EQVI':([5,9,10,11,16,22,23,24,25,30,31,32,33,34,],[21,-19,-20,-21,21,-16,-17,-18,21,-12,-13,-14,21,-22,]),'RPAREN':([9,10,11,22,23,24,25,30,31,32,33,34,],[-19,-20,-21,-16,-17,-18,34,-12,-13,-14,-15,-22,]),'END':([13,14,27,43,],[26,-5,-6,-7,]),'LBRACE':([15,],[28,]),'RBRACE':([28,36,37,38,42,],[-8,-10,39,-9,-11,]),'COMMA':([36,38,42,],[-10,40,-11,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'spec':([0,],[1,]),'kripkemodel':([0,],[2,]),'formulas':([2,],[4,]),'formula':([2,4,6,7,8,12,18,19,20,21,],[5,16,22,23,24,25,30,31,32,33,]),'worldlist':([3,],[13,]),'world':([3,13,],[14,27,]),'stringlist':([28,39,],[37,41,]),'stringlist1':([28,39,],[38,38,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> spec","S'",1,None,None,None),
  ('spec -> kripkemodel formulas','spec',2,'p_spec','modalparser.py',122),
  ('formulas -> formula SEMICOLON','formulas',2,'p_formulas_1','modalparser.py',129),
  ('formulas -> formulas formula SEMICOLON','formulas',3,'p_formulas_N','modalparser.py',133),
  ('kripkemodel -> MODEL worldlist END MODEL','kripkemodel',4,'p_kripkemodel','modalparser.py',145),
  ('worldlist -> world','worldlist',1,'p_worldlist_1','modalparser.py',154),
  ('worldlist -> worldlist world','worldlist',2,'p_worldlist_N','modalparser.py',158),
  ('world -> ID LBRACE stringlist RBRACE stringlist SEMICOLON','world',6,'p_world','modalparser.py',162),
  ('stringlist -> <empty>','stringlist',0,'p_stringlist_0','modalparser.py',166),
  ('stringlist -> stringlist1','stringlist',1,'p_stringlist_N','modalparser.py',170),
  ('stringlist1 -> ID','stringlist1',1,'p_stringlist_1','modalparser.py',174),
  ('stringlist1 -> stringlist1 COMMA ID','stringlist1',3,'p_stringlist_1N','modalparser.py',178),
  ('formula -> formula AND formula','formula',3,'p_formula_binop','modalparser.py',186),
  ('formula -> formula OR formula','formula',3,'p_formula_binop','modalparser.py',187),
  ('formula -> formula IMPL formula','formula',3,'p_formula_binop','modalparser.py',188),
  ('formula -> formula EQVI formula','formula',3,'p_formula_binop','modalparser.py',189),
  ('formula -> NOT formula','formula',2,'p_formula_unop_neg','modalparser.py',198),
  ('formula -> POSS formula','formula',2,'p_formula_unop_pos','modalparser.py',204),
  ('formula -> NECE formula','formula',2,'p_formula_unop_nec','modalparser.py',210),
  ('formula -> PTRUE','formula',1,'p_formula_true','modalparser.py',216),
  ('formula -> PFALSE','formula',1,'p_formula_false','modalparser.py',220),
  ('formula -> ID','formula',1,'p_formula_atom','modalparser.py',226),
  ('formula -> LPAREN formula RPAREN','formula',3,'p_formula_parentheses','modalparser.py',232),
]
