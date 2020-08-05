; https=//stackoverflow.com/questions/11604909/using-formulas-extract-an-os-version-number-from-a-variable-string/11605768%11605768
(set-logic SLIA)
(synth-fun f ((_arg_0 String)) String 
 ( (Start String (ntString)) 
 (ntString String (
	_arg_0
"" " " "BRD" "DRS" "LDS" "Branding" "Direct Response" "Leads" "=" "/" "in" "_" "9" "." "microsoft" "windows" "apple" "mac" "-" "1" "2" "3" "4" "5" "6" "7" "8" "0" "," "<" ">" "/n" "%" "b" "apple" "bananas" "strawberries" "oranges" "LLC" "Inc" "Corporation" "Enterprises" "Company" "(" ")" "+" "name" ","
	(str.++ ntString ntString) 
	(str.replace ntString ntString ntString) 
	(str.at ntString ntInt)
	(int.to.str ntInt)
	(ite ntBool ntString ntString)
	(str.substr ntString ntInt ntInt)
)) 
 (ntInt Int (
-1 1 2 3 4 5 6 7 8 9 0
	1 0 -1 1
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
(constraint (= (f "AIX 5.1") "5.1"))
(constraint (= (f "VMware ESX Server 3.5.0 build-110268") "3.5"))
(constraint (= (f "Linux Linux 2.6 Linux") "2.6"))
(constraint (= (f "Red Hat Enterprise AS 4 <2.6-78.0.13.ELlargesmp>") "2.6"))
(constraint (= (f "Microsoft <R> Windows <R> 2000 Advanced Server 1.0") "1.0"))
(constraint (= (f "Microsoft Windows XP Win2008R2 6.1.7601") "6.1"))
(check-synth)
