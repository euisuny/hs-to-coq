Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import String.
From QuickChick Require Import QuickChick.

Require DeepWeb.Test.ExternalTest.

Definition test0 := print_extracted_coq_string ("Checking ExternalTest.execute_prop..." ++ newline ++ show (quickCheckWith (updMaxSuccess stdArgs 100) ExternalTest.execute_prop))%string.

Separate Extraction test0.

