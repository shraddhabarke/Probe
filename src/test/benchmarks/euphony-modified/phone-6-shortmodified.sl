(set-logic SLIA)
(synth-fun f ((name String)) String
    ((Start String (ntString))
     (ntString String (name " " "+" "-" "."
(str.++ ntString ntString)
(str.replace ntString ntString ntString)
    " " "" "%" "(" ")" "+" "" "-" "." "/" "/n" "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "9999999" "<" "=" ">" "BRD" "Branding" "C0" "CA" "CT" "Company" "Corporation" "DRS" "Direct Response" "Dr." "Enterprises" "Inc" "LDS" "LLC" "Leads" "MD" "NY" "Name" "PA" "USA" "_" "_acme.com" "apple" "b" "bananas" "blue" "boo" "green" "in" "mac" "microsoft" "orange" "oranges" "other" "overhead" "pink" "some project" "ssp." "strawberries" "that" "windows" "yellow" "|"
(int.to.str ntInt)
(ite ntBool ntString ntString)
(str.substr ntString ntInt ntInt)
))
      (ntInt Int (0 1 2 3 4 5
(+ ntInt ntInt)
(- ntInt ntInt)
(str.len ntString)
(str.to.int ntString)
(str.indexof ntString ntString ntInt)
))
(ntBool Bool (true false
(= ntInt ntInt)
(str.prefixof ntString ntString)
(str.suffixof ntString ntString)
(str.contains ntString ntString)
))
))
(constraint (= (f "+106 769-858-438") "769"))
(constraint (= (f "+83 973-757-831") "973"))
(constraint (= (f "+62 647-787-775") "647"))
(constraint (= (f "+172 027-507-632") "027"))
(constraint (= (f "+72 001-050-856") "001"))
(constraint (= (f "+95 310-537-401") "310"))
(constraint (= (f "+6 775-969-238") "775"))

(check-synth)
