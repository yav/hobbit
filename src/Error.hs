module Error where


bug f msg   = error ("Bug detected in function \"" ++ f ++ "\":\n\t" ++ msg)

unexpected f msg  = bug f ("Unexpected " ++ msg)
                  






