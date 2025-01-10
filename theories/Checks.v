From OGS Require Import Prelude.
From OGS.Ctx Require Import All Subst.
From OGS.OGS Require Import Game Strategy.
From OGS.OGS Require Soundness.
From OGS.Examples Require STLC_CBV ULC_CBV SystemL_CBV SystemD.

Module generic.
  Import Soundness.
Goal True.
  idtac "=============================".
  idtac "Generic OGS soundness theorem".
  idtac "=============================".
  idtac "1. Arguments and type".
  idtac "-----------------------------".
Abort.
About Soundness.ogs_correction.
Goal True.
  idtac "--------------".
  idtac "2. Assumptions".
  idtac "--------------".
Abort.
Print Assumptions Soundness.ogs_correction.
End generic.

Module stlc.
Import STLC_CBV.
Goal True.
  idtac "===================================================".
  idtac " Simply-typed lambda-calculus OGS soundness theorem".
  idtac "===================================================".
  idtac "1. Arguments and type".
  idtac "---------------------------------------------------".
Abort.
About STLC_CBV.stlc_ciu_correct.
Goal True.
  idtac "--------------".
  idtac "2. Assumptions".
  idtac "--------------".
Abort.
Print Assumptions STLC_CBV.stlc_ciu_correct.
End stlc.

Module ulc.
Import ULC_CBV.
Goal True.
  idtac "==============================================".
  idtac " Untyped lambda-calculus OGS soundness theorem".
  idtac "==============================================".
  idtac "1. Arguments and type".
  idtac "----------------------------------------------".
Abort.
About ULC_CBV.ulc_ciu_correct.
Goal True.
  idtac "--------------".
  idtac "2. Assumptions".
  idtac "--------------".
Abort.
Print Assumptions ULC_CBV.ulc_ciu_correct.
End ulc.

Module systeml.
Import SystemL_CBV.
Goal True.
  idtac "===================================".
  idtac " CBV System L OGS soundness theorem".
  idtac "===================================".
  idtac "1. Arguments and type".
  idtac "-----------------------------------".
Abort.
About SystemL_CBV.ciu_correct.
Goal True.
  idtac "--------------".
  idtac "2. Assumptions".
  idtac "--------------".
Abort.
Print Assumptions SystemL_CBV.ciu_correct.
End systeml.

Module systemd.
Import SystemD.
Goal True.
  idtac "=========================================".
  idtac " Polarized System D OGS soundness theorem".
  idtac "=========================================".
  idtac "1. Arguments and type".
  idtac "-----------------------------------------".
Abort.
About SystemD.ciu_correct.
Goal True.
  idtac "--------------".
  idtac "2. Assumptions".
  idtac "--------------".
Abort.
Print Assumptions SystemD.ciu_correct.
End systemd.
