; https=//stackoverflow.com/questions/25239569/excel-function-to-match-a-substring-from-text-with-a-list
(set-logic SLIA)
(synth-fun f ((_arg_0 String)) String 
 ( (Start String (ntString)) 
 (ntString String (
	_arg_0
    " " "" "%" "(" ")" "+" "" "-" "." "/" "/n" "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "9999999" "<" "=" ">" "BRD" "Branding" "C0" "CA" "CT" "Company" "Corporation" "DRS" "Direct Response" "Dr." "Enterprises" "Inc" "LDS" "LLC" "Leads" "MD" "NY" "Name" "PA" "USA" "_" "_acme.com" "apple" "b" "bananas" "blue" "boo" "green" "in" "mac" "microsoft" "orange" "oranges" "other" "overhead" "pink" "some project" "ssp." "strawberries" "that" "windows" "yellow" "|"
	(str.++ ntString ntString) 
	(str.replace ntString ntString ntString) 
	(str.at ntString ntInt)
	(int.to.str ntInt)
	(ite ntBool ntString ntString)
	(str.substr ntString ntInt ntInt)
)) 
 (ntInt Int (
	
	1 0 -1
	(+ ntInt ntInt)
	(- ntInt ntInt)
	(str.len ntString)
	(str.to.int ntString)
	(ite ntBool ntInt ntInt)
	(str.indexof ntString ntString ntInt)
)) 
 (ntBool Bool (
	
	true false
	(= ntInt ntInt)
	(str.prefixof ntString ntString)
	(str.suffixof ntString ntString)
	(str.contains ntString ntString)
)) ))
(constraint (= (f "Adf_ROCLeader_BAN_728x90_CPM_STD _BRD _NRT_DCK") "Adf_ROCLeader_BAN_728x90_CPM_STD _Branding _NRT_DCK"))
(constraint (= (f "MMC_ContextualLarRec_BAN_336x280_CPM_STD _LDS _RTG_DCK") "MMC_ContextualLarRec_BAN_336x280_CPM_STD _Leads _RTG_DCK"))
(constraint (= (f "Adf_ROC_DLBD_728x90_CPM_STD_DRS_NRT_NOR_DCK") "Adf_ROC_DLBD_728x90_CPM_STD_Direct Response_NRT_NOR_DCK"))
(check-synth)
