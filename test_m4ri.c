#include <m4ri/mzd.h>
#include <stdio.h>

int main() {
    mzd_t *A = mzd_init(4, 4);
    if (A) {
        printf("M4RI library works! Matrix created successfully.\n");
        mzd_write_bit(A, 0, 0, 1);
        printf("Bit written: %d\n", mzd_read_bit(A, 0, 0));
        mzd_free(A);
        return 0;
    } else {
        printf("Failed to create matrix - M4RI not working properly\n");
        return 1;
    }
}
