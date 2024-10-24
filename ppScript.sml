open preamble deadlockFreedomTheory richerLangTheory envSemTheory

val _ = new_theory "pp";

val OMIT_def = Define `OMIT x = x`
val HIDE_def = Define `HIDE x = x`

val _ = remove_ovl_mapping "S" {Name = "S", Thy = "combin"}

(*
Theorem better_trans_let:
  OPT_MMAP (λv. FLOOKUP s (v,p)) varvec = SOME valvec ⇒
  trans (s, Let v p e c) (LLet v p f varvec, [])
        (s |+ ((v,p), f valvec), c)
Proof
  strip_tac >>
  ‘EVERY IS_SOME (MAP (FLOOKUP s) (MAP (λv. (v,p)) varvec))’
    by (pop_assum mp_tac >> qid_spec_tac ‘valvec’ >> Induct_on ‘varvec’ >>
        simp[OPT_MMAP_def, PULL_EXISTS]) >>
  drule_then (qspecl_then [‘v’, ‘f’, ‘c’] strip_assume_tac)
             chorSemTheory.trans_let >>
  ‘MAP (THE o FLOOKUP s) (MAP (λv. (v,p)) varvec) = valvec’
    suffices_by (strip_tac >> gs[]) >>
  last_x_assum mp_tac >> rpt (pop_assum kall_tac) >>
  qid_spec_tac ‘valvec’ >> Induct_on ‘varvec’ >>
  simp[OPT_MMAP_def, PULL_EXISTS]
QED
*)                                                
Theorem better_trans_submap =
        chorPropsTheory.trans_submap
          |> Q.SPECL [‘z1’, ‘c’, ‘α’, ‘τ’, ‘z1'’, ‘c'’, ‘z2’]

Theorem better_Trm_trans =
        chorPropsTheory.Trm_trans
          |> Q.SPECL [‘s’, ‘c’, ‘τ’, ‘k’, ‘(s',c')’]
          |> REWRITE_RULE [chorPropsTheory.no_undefined_vars_def]                                            
Theorem better_chortype_no_undefined_vars =
        chorTypePropsTheory.chortype_no_undefined_vars
          |> Q.SPECL [‘Γ’, ‘Θ’, ‘s’]
          |> REWRITE_RULE [chorPropsTheory.no_undefined_vars_def]                                            
Theorem better_chor_preservation_lemma =
        deadlockFreedomTheory.chor_preservation_lemma
          |> Q.SPECL [‘c’, ‘Θ’, ‘Γ’, ‘s’, ‘τ’, ‘l’, ‘s'’, ‘c'’]
          |> REWRITE_RULE [chorPropsTheory.not_finish_def]
                                                
Theorem better_chor_progress_lemma =
        deadlockFreedomTheory.chor_progress_lemma
          |> Q.SPECL [‘c’, ‘s’]
          |> REWRITE_RULE [chorPropsTheory.not_finish_def]
                                                
Theorem better_trans_letval =
        chorSemTheory.trans_letval |> Q.SPECL [‘v’, ‘s’, ‘x’, ‘p’, ‘e’, ‘c’, ‘cl’]
                                   |> REWRITE_RULE [localise_fdom]

Theorem better_trans_letexn =
        chorSemTheory.trans_letexn |> Q.SPECL [‘s’, ‘x’, ‘p’, ‘e’, ‘c’, ‘cl’, ‘exn’]
                                   |> REWRITE_RULE [localise_fdom] 

Theorem better_lcong_reord =
  chorSemTheory.lcong_reord |> Q.SPECL [‘[]’, ‘[]’, ‘α’, ‘β’]
                            |> REWRITE_RULE [DISJOINT_DEF, APPEND_NIL, APPEND]

fun chain stem n =
  let
    fun mk i = TOK ("(" ^ stem ^ Int.toString i ^ ")")
    fun recurse A i = if i = 0 then A
                        else recurse (mk i :: TM :: A) (i - 1)
  in
    recurse [mk n] (n - 1)
  end


Overload BZERO = “chorLang$Nil”;

Overload listNIL = “list$NIL”

Overload chortrans = “λs1 c1 l t s2 c2. chorSem$trans (s1,c1) (l,t) (s2,c2)”
Overload nillabs = “[] : chorSem$label list”

fun stdrule (n,f,els) =
  add_rule{term_name = n, fixity = f, pp_elements = els,
           paren_style = OnlyIfNecessary,
           block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))}

(*
val _ = stdrule ("BinOp", Infixl 500,
                 [TOK "ws", TM, TOK "ws"]);
*)

Overload LENSUPD = “λfm k v. fm |+ (k,v)”

val _ = stdrule ("LENSUPD", Suffix 2100, chain "LENSUPD" 3)
                           
Overload DELETEX = “λS x. S DELETE x”

val _ = stdrule ("DELETEX", Suffix 451, chain "DELETEX" 2)

Overload fdomm = “λf. FDOM f”

val _ = stdrule ("fdomm", Closefix, chain "fdom" 2)

Overload drestrict = “λf A. DRESTRICT f A”

val _ = stdrule ("drestrict", Suffix 451, chain "drestrict" 2)

val _ = stdrule ("Fix", Prefix 501,
                 [TOK "(fixmu)", TM, TOK "(fixdot)", BreakSpace(1,2)]);

val _ = stdrule
        ("IfThen", Prefix 501,
         [PPBlock([PPBlock([PPBlock([TOK "(ifth1)", BreakSpace(1,2), TM,
                                     TOK "(ifth2)", TM],
                                    (PP.CONSISTENT, 0)),
                            BreakSpace(1,0),
                            TOK "(ifth3)"],
                           (PP.CONSISTENT, 0)),
                   BreakSpace(1,2),
                   TM], (PP.CONSISTENT, 0)),
          BreakSpace(1,0),
          BeginFinalBlock (PP.CONSISTENT, 0),
          TOK "(ifth4)", BreakSpace(1,2)])

Overload "Com'" = “chorLang$Com”
Overload "Com0" = “λp1 v1 p2 v2. chorLang$Com p1 v1 p2 v2 Nil”
val _ = stdrule ("Com'", Prefix 501,
                 [TOK "(com1)", TM, TOK "(com2)", TM,
                  TOK "(com3)", TM, TOK "(com4)", TM,
                  TOK "(com5)"]);
val _ = stdrule ("Com0", Closefix, chain "com0" 5)

val _ = stdrule ("Let", Prefix 501,
                 [TOK "(let1)", TM, TOK "(let2)", TM,
                  TOK "(let3)", TM, TOK "(let4)", TM,
                  TOK "(let5)"]);

val _ = stdrule ("Sel", Prefix 501,
                 [TOK "(sel1)", TM, TOK "(sel2)", TM,
                  TOK "(sel3)", TM, TOK "(sel4)"]);

val _ = stdrule ("Call", Closefix, [TOK "(call1)", TM, TOK "(call2)"]);

val _ = stdrule ("chortrans", Closefix,
                 [TOK "(chortrans1)", TM, TOK "(chortrans2)", TM,
                  TOK "(chortrans3)", TM, TOK "(chortrans4)", TM,
                  TOK "(chortrans5)", TM, TOK "(chortrans6)", TM,
                  TOK "(chortrans7)"]);

val _ = add_rule {term_name =  "chorTypecheckOK", fixity = Suffix 451,
                  paren_style=  OnlyIfNecessary, 
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,0)),
                  pp_elements = [TOK "comma", TM, TOK "vdash", TM, TOK "checkmark"]}

(*
val _ = stdrule ("localise", Prefix 501,
                 [TOK "(localise1)", TM, TOK "comma", TM, TOK "(localise3)"]);
*)
val _ = stdrule ("free_variables", Closefix,
                 [TOK "(fvs1)", TM, TOK "(fvs2)"]);

val _ = stdrule ("free_vars", Closefix,
                 [TOK "(fvs1)", TM, TOK "(fvs2)"]);
               
val _ = add_rule {term_name =  "typecheck", fixity = Suffix 451,
                  paren_style=  OnlyIfNecessary, 
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,0)),
                  pp_elements = [TOK "vdash_s", TM, TOK "colon"]}

val _ = add_rule {term_name =  "value_type", fixity = Prefix 501,
                  paren_style=  OnlyIfNecessary, 
                  block_style = (AroundEachPhrase, (PP.CONSISTENT,0)),
                  pp_elements = [TOK "(vt1)", TM, TOK "(vt2)"]}                                                                        
                              
val _ = add_rule {term_name = "LCom", fixity = Infixr 400,
                  paren_style = IfNotTop{realonly=false},
                  block_style = (AroundEachPhrase,(PP.CONSISTENT,0)),
                  pp_elements =
                  [TOK "(lcom1)", TM, TOK "(lcom2)", TM, TOK "(lcom3)"]}

Overload LSel' = “λp1 p2 b. chorSem$LSel p1 b p2”
val _ = add_rule {term_name = "LSel'", fixity = Suffix 420,
                  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = IfNotTop{realonly=false},
                  pp_elements =
                  [TOK "(lsel1)", TM, TOK "(lsel2)", TM, TOK "(lsel3)"]};

Overload lookupEQ = “λf x y. FLOOKUP f x = SOME y”
val _ = stdrule ("lookupEQ", Infix(NONASSOC, 450), chain "lookupeq" 2)

Overload bareLookup = “λf x. FLOOKUP f x”
val _ = stdrule ("bareLookup", Infix(NONASSOC, 450), chain "bareLookup" 1);

Overload writtenNEQ = “λx y. written x ≠ SOME y”
val _ = stdrule ("writtenNEQ", Prefix 2101, chain "writtenNEQ" 2)

Overload optmapEQ = “λf x y. OPT_MMAP f x = SOME y”
val _ = stdrule ("optmapEQ", Prefix 2101, chain "optmapEQ" 3)

val _ = stdrule ("written", Closefix, chain "written" 2)
val _ = stdrule ("LTau", Closefix, chain "ltau" 3)
val _ = stdrule ("freeprocs", Closefix, chain "freeprocs" 2)
val _ = stdrule ("dsubst", Suffix 2100, chain "dsubst" 3)
val _ = stdrule ("LLet", Prefix 2101, chain "llet" 4)

val _ = stdrule ("Send", Prefix 2101, chain "send" 3)
val _ = stdrule ("Receive", Prefix 2101, chain "receive" 3)

val _ = set_fixity ";;" (Infixr 502)

val _ = export_theory();
