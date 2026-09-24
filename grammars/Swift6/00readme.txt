Swift 6 grammar Document Revision History 2024-09-16

Provenance

1. Copy from screen at https://docs.swift.org/swift-book/documentation/the-swift-programming-language/summaryofthegrammar and paste into MS Word, saved as Swift6Grammar.docx

2. Save copy as Swift6GrammarDraft.docx

3. Edit Swift6GrammarDraft.docx in MS Word:
	Remove section headers
	Replaced paragraph mark with newline
	Enclosed bold keywords in quotation marks "
	Replaced → with =
	Removed - in names and applied camel capitalization
	Added a . after each rule
	Removed spurious \s near declaration and expression	

4. Save a copy as Swift6Grammar.apus
	Rewrite whitespace, comment, identifier and various Unicode character ranges as Regex or Swift String literal
	Assume the file has already been successfully parsed by the Swift compiler, so that terminal definitions do not need to be 100%, only need to avoid to overmatch.
	Rewrite terminals as Regex's
	Replaced curly quotes with straight quotes "
	Replaced non-ascii spaces with ' '
	Added an escape for every \ in literals
	Capitalized Operator rule to avoid conflict with "operator" literal

5. 
