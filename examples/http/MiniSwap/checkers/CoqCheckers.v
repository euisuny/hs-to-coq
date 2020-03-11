Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import String.
From QuickChick Require Import QuickChick.

Require DeepWeb.Test.TestCLikeSpec.

Definition test0 := print_extracted_coq_string ("Checking TestCLikeSpec.SingleSwap.test..." ++ newline ++ show (quickCheck TestCLikeSpec.SingleSwap.test))%string.

Definition test1 := print_extracted_coq_string ("Checking TestCLikeSpec.test..." ++ newline ++ show (quickCheck TestCLikeSpec.test))%string.

Separate Extraction test0 test1.
