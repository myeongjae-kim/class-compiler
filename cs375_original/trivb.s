#Symbol table level 1
# 26975216           i  VAR    0 typ integer  lvl  1  siz     4  off     0
# 26975312         lim  VAR    0 typ integer  lvl  1  siz     4  off     4
# token 26977264  OP       program  dtype  0  link 0  operands 26974448
#(program graph1 (progn output)
#                (progn (:= lim 7)
#                       (progn (:= i 0)
#                              (label 0)
#                              (if (<= i lim)
#                                  (progn (funcall writeln '*')
#                                         (:= i (+ i 1))
#                                         (goto 0))))))
# ---------------- Beginning of Generated Code --------------------
        .file   "foo"
        .text
.globl graph1
        .type   graph1, @function
graph1:
.LFB0:
	.cfi_startproc
	pushq	%rbp              # save base pointer on stack
	.cfi_def_cfa_offset 16
	movq	%rsp, %rbp        # move stack pointer to base pointer
	.cfi_offset 6, -16
	.cfi_def_cfa_register 6
        subq	$32, %rsp 	  # make space for this stack frame
	movq	%rbx, %r9        # save %rbx (callee-saved) in %r9
# ------------------------- begin Your code -----------------------------
	movl	$7,%eax         	#  7 -> %eax
	movl	%eax,-28(%rbp)     	#  %eax -> lim
	movl	$0,%eax         	#  0 -> %eax
	movl	%eax,-32(%rbp)     	#  %eax -> i
.L0:
	movl	-32(%rbp),%eax     	#  i -> %eax
	movl	-28(%rbp),%ecx     	#  lim -> %ecx
	cmpl	%ecx,%eax           	#  compare %eax - %ecx
	jle	.L2 			#  jump if     <=
	jmp	.L3 			#  jump 
.L2:
	movl	$.LC4,%edi       	#  addr of literal .LC4
	call	writeln              	#  writeln()
	movl	-32(%rbp),%eax     	#  i -> %eax
	movl	$1,%ecx         	#  1 -> %ecx
	addl	%ecx,%eax         	#  %eax + %ecx -> %eax
	movl	%eax,-32(%rbp)     	#  %eax -> i
	jmp	.L0 			#  jump 
.L3:
# ----------------------- begin Epilogue code ---------------------------
	movq	%r9, %rbx        # restore %rbx (callee-saved) from %r9
        leave
        ret
        .cfi_endproc
.LFE0:
        .size   graph1, .-graph1
# ----------------- end Epilogue; Literal data follows ------------------
        .section        .rodata
	.align  4
.LC4:
	.string	"*"

        .ident  "CS 375 Compiler - Spring 2018"
