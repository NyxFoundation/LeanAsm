.intel_syntax noprefix
.text
.globl check_preserved
.type check_preserved, @function
check_preserved:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    sub rsp, 8
    mov rbx, 11
    mov rbp, 22
    mov r12, 33
    mov r13, 44
    mov r14, 55
    mov r15, 66
    call abi_body
    cmp rax, 1
    jne failed
    cmp rbx, 11
    jne failed
    cmp rbp, 22
    jne failed
    cmp r12, 33
    jne failed
    cmp r13, 44
    jne failed
    cmp r14, 55
    jne failed
    cmp r15, 66
    jne failed
    jmp restore
failed:
    xor eax, eax
restore:
    add rsp, 8
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret
.size check_preserved, . - check_preserved
.section .note.GNU-stack,"",@progbits
