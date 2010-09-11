syntax case match

syntax keyword bitKeyword area as bitdata data deriving do case else 
syntax keyword bitKeyword if import in let module of 
syntax keyword bitKeyword struct primitive then type where 

syntax match bitName "[A-Za-z][A-Za-z0-9_']*"

syntax match bitComment "--.*"
syntax region bitComment start="{-" end="-}" contains=bitComment

syntax match bitLiteral "B\(0\|1\)\+\|0[xX][0-9a-fA-F]\+\|[0-9]\+[KMG]\?"
syntax region bitString start=/"/ skip=/\\"/ end=/"/

highlight link bitKeyword Keyword
highlight link bitOperator Operator
highlight link bitComment Comment
highlight link bitLiteral Number
highlight link bitString String
highlight link bitType Type


