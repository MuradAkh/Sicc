#include <stdio.h>

int main(int x, char z){
    int x = 0;
    int y = 0;
    x = 1;
    x = y;

    while (x)
    {
        // assert(1);
        while (x)
        {
            x = 42;
        }
        
        x = 2;
        x = 3;
        x = 4;
        assert(1);
        x = 5;
        while (y)
        {
            y = 2;
            y = 3;
            z = 1;
        }
        
    }
    

    
}

