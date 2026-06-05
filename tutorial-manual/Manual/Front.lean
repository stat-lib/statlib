import Manual.Pages.Installation
import Manual.Pages.RiskKernels
import Manual.Pages.QMD
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Statlib" =>
%%%
authors := []
shortTitle := "Statlib"
%%%

These tutorial pages develop the decision-theoretic setup for statistical
inference.

{include 0 Manual.Pages.Installation}

{include 1 Manual.Pages.RiskKernels}

{include 1 Manual.Pages.QMD}
