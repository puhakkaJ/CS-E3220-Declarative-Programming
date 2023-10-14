
#!/usr/bin/python3

import sys

# Read satreachability output and visualize game of life

def main():
    xMax = 0
    yMax = 0
    tMax = 0
    cells = set()
    for s in sys.stdin: #while 1==1:
        if s.startswith("Transition sequence:"):
            break
        if s.startswith("cell_"):
#            print(s)
            tokens = s.split()
            if len(tokens) == 3:
                numbers = tokens[0].split("_")
                if len(numbers) == 4:
#                    print("X = " + numbers[1] + " Y = " + numbers[2] + " t = " + numbers[3])
                    x = int(numbers[1])
                    y = int(numbers[2])
                    t = int(numbers[3])
                    xMax = max(x,xMax)
                    yMax = max(y,yMax)
                    tMax = max(t,tMax)
                    if tokens[2].startswith("True"):
                        cells.add( (x,y,t) )
    if len(cells) == 0:
        print("No solution")
        exit(0)
    for t in range(0,tMax+1):
        print("Grid at time " + str(t) + ":")
        for y in range(0,yMax+1):
            for x in range(0,xMax+1):
                if (x,y,t) in cells:
                    print("X",end='')
                else:
                    print(".",end='')
            print("")
        print("")

main()
