import GotoLean.Audit
import Proofs.TakeWord

#check_axioms ParserContracts.copy_word_correct
#check_axioms ParserContracts.copy_word_call
#check_axioms ParserContracts.take_word_rule
#check_axioms TokenParser.verify
#check_axioms TokenParser.success
#check_axioms TokenParser.rejected
#check_axioms GotoLean.Memory.readBits_writeBits_word
#check_axioms GotoLean.Memory.readByte_written_frame
