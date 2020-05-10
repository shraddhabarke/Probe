; https=//stackoverflow.com/questions/28616046/excel-substrings/28618923%28618923
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
(constraint (= (f "valentine day=1915=50==7.1=45") "valentine day"))
(constraint (= (f "movie blah=2blahblah, The=1914=54==7.9=17") "movie blah=2blahblah, The"))
(check-synth)
