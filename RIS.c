#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
#define NOT_EXIST 0xFFFF;
#define LARGE 170
#define MAX_ITERATION 10 // Max tests in Miller-Robin Primality Test.
#define div /
#define mod %
#define and &&
#define true 1
#define false 0
/***********RSA head********/
#define STACK_SIZE 10000
#define NOT_EXIST 0xFFFF;
int print_flag=0;
#define LAMDA 100 


/****ends*******/  
typedef struct{
int top;
char c[STACK_SIZE];
} stack;
stack s;
typedef struct 
{
  int x; /* x-coordinate of sensor node location in target field */
  int y; /* y-coordinate of sensor node location in target field */
  int *keyring; /* key ring */
  int phynbrsize; /* number of physical neighbors of a sensor node */
  int keynbrsize; /* number of key neighbors of a sensor node */
  int *phynbr; /* List of physical neighbors of a sensor node */
  int *keynbr; /* List of key neighbors of a sensor node */
} sensor;
int n,total_path_key_one_hop_count=0,total_path_key_two_hop_count =0;
sensor sensor_node[600];
float average_neighbour_size=0.0,total_key=0.0, total_physical=0.0;
long int D[LAMDA+1][LAMDA+1];
long int G[LAMDA+1][600];
void creatematrix_D(){
int i,j;
int count=1;
for(i=0;i<LAMDA+1;i++)
{
	for(j=i;j<LAMDA+1;j++,count++)
           D[i][j]=count+i+j;

}

for(i=0;i<LAMDA+1;i++)
{
	for(j=0;j<i;j++)
           D[i][j]=D[j][i];

}

}


void reverse_string(char x[])
{
int n = strlen(x)-1;
int i = 0;
char temp[STACK_SIZE];
for(i = 0; i<=n; i++)
 temp[i] = x[n-i];
for(i=0; i<=n; i++)
 x[i] = temp[i];
}

void decimal_to_binary(long int n,char str[])
{
// n is the given decimal integer.
// Purpose is to find the binary conversion
// of n.
 // Initialise the stack.
int r;
 s.top = 0;
while(n != 0)
{
r = n mod 2;
s.top++;
if(s.top >= STACK_SIZE)
{
printf("\nstack overflown!\n");
return;
}
s.c[s.top] = r + 48;
if(print_flag)
 printf("\n s.c[%d]= %c\n", s.top, s.c[s.top]);
n = n div 2;
}
while(s.top)
{
 *str++ = s.c[s.top--];
}
*str='\0';
return;
}
//munmun
long int ModPower(long int x, long int e, long int n)
{
// To calculate y:=x^e(mod n).
 //long y;
 long int y;
long int t;
 int i;
int BitLength_e;
char b[STACK_SIZE];
 //printf("e(decimal) = %ld\n",e);
decimal_to_binary(e,b);
if(print_flag)
 printf("b = %s\n", b);
BitLength_e = strlen(b);
y = x;
reverse_string(b);
for(i = BitLength_e - 2; i >= 0 ; i--)
{
if(print_flag)
 printf("\nb[%d]=%c", i, b[i]);
if(b[i] == '0')
t = 1;
else t = x;
 y = (y * y) mod n;
 if ( y < 0 ) {
 y = -y;
 y = (y - 1) * (y mod n) mod n;
 //printf("y is negative\n");
 }
y = (y*t) mod n;
 if ( y < 0 ) {
 y = -y;
 y = (y - 1) * (y mod n) mod n;
 //printf("y is negative\n");
 }
}
 if ( y < 0 ) {
 y = -y;
 y = (y - 1) * (y mod n) mod n;
// printf("y is negative\n");
 }
return y;

}
/******ens**********/
/* Connect with the server: socket() and connect() */
void creatematrix_G(long int g,long int q)
{
int i,j,k,l,cal1=1,cal2,cal3=1,cal4;

for(i=0;i<LAMDA+1;i++)
{
for(j=0;j<n;j++)
{
	if(i==0)
	G[i][j]=1;
	else
	{
	 long int temp=ModPower( g,j+1,q);
         G[i][j]=ModPower(temp,i,q);
                 
	}
}

}
for(i=0;i<LAMDA+1;i++)
{
for(j=0;j<n;j++)
{
printf("%ld\t",G[i][j]);
}
printf("\n");
}


}
int primitiveroot(long int q)
{
long int hash[q+10];
long int g,n,flag,i,temp=1,temp2,k;
for(g=2; g<q; g++)
	{
	memset(hash, 0, sizeof(hash));
	for(n=1; n<q; n++)
		{
                long int temp=ModPower( g,n,q);
		 
		 hash[temp]=1;
		}
	flag=1;
	for(i=1; i<q; i++)
		{
		if(hash[i]!=1)
			flag=0;
		}
	if(flag==1)
		return g;
	}

}
//Munmun
int MillerRobinTest(long int n, int iteration)
{
// n is the given integer and k is the given desired
// number of iterations in this primality test algorithm.
// Return true if all the iterations test passed to give
// the higher confidence that n is a prime, otherwise
// return false if n is composite.
long int m, t;
 int i,j;
long int a, u;
 int flag;
 if(n mod 2 == 0)
return false; // n is composite.
 m = (n-1) div 2;
 t = 1;
while( m mod 2 == 0) // repeat until m is even
 {
 m = m div 2;
 t = t + 1;
 }

 for (j=0; j < iteration; j++) { // Repeat the test for MAX_ITERATION times
 flag = 0;
 srand((unsigned int) time(NULL));
 a = random() mod n + 1; // select a in {1,2,......,n}
 u = ModPower(a,m,n);
 if (u == 1 || u == n - 1)
 flag = 1;
for(i=0;i<t;i++)
 {
 if(u == n - 1)
 flag = 1;
 u = (u * u) mod n;
 }
 if ( flag == 0 )
 return 0; // n is composite
 }
return 1; // n is prime.
} 
double distance_cal(int x1, int y1, int x2, int y2)
{  

  double diffx,diffy,diffx_sqr,diffy_sqr;
  diffx = x1 - x2;
  diffx_sqr = pow(diffx, 2);
  diffy = y1 - y2;
  diffy_sqr = pow(diffy, 2); 
  return sqrt (diffx_sqr + diffy_sqr);
}

void generating_random_numbers(int keyring_size,FILE *fp2, int keypool_size)
{
  
  char str[15];
  int i, j, x, y, index, n1, n2,flag=0, key1,fkey_ring=0;
  time_t t;
  srand((unsigned) time(&t));
  sprintf(str, "%d", n);
  fprintf(fp2,"%s\n", str);
  //allocation of x-y values and keyring
  for(i=0; i<n; ++i)
            {
            n1 = rand() % 500 + 1;
            n2 = rand() % 500 + 1; 	
            flag=0;
            for(j=0; j<i; ++j)
                    {
                      if(sensor_node[j].x == n1 && sensor_node[j].y == n2)
                              {
                              	--i;
                                flag=1;
                                break;
                              }
                    }
            if(flag==0)
                  {
                      sensor_node[i].x = n1;
                      sprintf(str, "%d", n1);
                      fprintf(fp2,"%s ", str);
                      sensor_node[i].y = n2;
	                  sprintf(str, "%d", n2);
                      fprintf(fp2,"%s\n", str);
                  }           
            sensor_node[i].keyring =(int*)malloc(keyring_size*sizeof(int));
            for(x=0; x<keyring_size; ++x)
                {
                  key1 = rand() % keypool_size + 1;
                  fkey_ring=0;
                  for(y=0; y<x; ++y)
                      {
                      if (*(sensor_node[i].keyring + y) == key1)
                            {
                              fkey_ring=1;
                              --x;
                              break;
                            }    
                      }
                  if(fkey_ring==0)
                      *(sensor_node[i].keyring + x) = key1;
                }
            }
  fclose(fp2);
}
void finding_physical_and_key_neighbours(int keyring_size)
{

	double distance ,total_distance=0.0,physical_neighbour_size=0.0;
	int i=0, x=0;
	for(i=0; i<n; ++i)
        {
        	int phy_neighbours_array[100000]; 
        	sensor_node[i].phynbrsize=0;
        	int j;
        	for (j = 0; j < n; ++j)
        	{
        		if (i==j)
        		{
        			continue;
        		}
        		int x1,x2,y1,y2;
        		x1=sensor_node[i].x;
        		y1=sensor_node[i].y;
        		x2=sensor_node[j].x;
        		y2=sensor_node[j].y;
        		distance =distance_cal(x1, y1, x2,y2);

        		if(25.00>=distance)
        		{
        			
        			phy_neighbours_array[sensor_node[i].phynbrsize] = j;
        			++sensor_node[i].phynbrsize;
        		}
            if(j>i)
            total_distance = total_distance + distance;
        	}
        physical_neighbour_size=physical_neighbour_size+sensor_node[i].phynbrsize;
        sensor_node[i].phynbr  =(int*)malloc(sensor_node[i].phynbrsize*sizeof(int));
        int k;
        int phy_nbr_size=sensor_node[i].phynbrsize;
        for(k=0; k<phy_nbr_size; ++k)
         {
          *(sensor_node[i].phynbr+k) = phy_neighbours_array[k];
         }

        }
//average_neighbour_size = physical_neighbour_size/n;        
//printf("Scaling communication range...\nAverage distance = %f\nCommunication range of sensor nodes = 25.00\nComputing physical neighbors...\n",total_distance/((n-1)*(n/2) ));   
//printf("Average neighborhood size = %f\n", average_neighbour_size);
//finding_key_neighbours(keyring_size);        
}

int main( int argc, char *argv[] )  
{
	if(argc==2)
	{
	printf("Enter the no of sensor nodes\n");
	int argument_2,argument_3;
	char argument_1[100],string[10000]="plot[0:500][0:500] \"";
	memset(argument_1, '\0', sizeof(argument_1));
	strcpy(argument_1,argv[1]);
	strcat(string, argument_1);
  strcat(string, "\" every ::1 using 1:2");
	scanf("%d",&n);
	FILE *fp1;
   fp1=fopen("mun", "w");
    fprintf(fp1,"%s", string);
    fclose(fp1);
    //fprintf(fp1,"%s", string);
	FILE *fp;
    fp=fopen(argument_1, "w");
    if(fp==NULL) 
      {
        perror("Error opening file.");
      }
    argument_2=100;
    argument_3=40000;  
    generating_random_numbers(argument_2,fp,argument_3);
    finding_physical_and_key_neighbours(argument_2);
    //printing_sensor_nodes(argument_2);
   // simulating_path_key_establishment(argument_2,argument_3);
   // finding_network_connectivity(argument_2,argument_3);
    }

    else
    {
    	printf("invalid number of arguments\n");
    	exit(0);
    }
	system("gnuplot -p 'mun'"); 
long int q;
printf("\n selecting prime->\n\r");
while(1)
{
 srand((unsigned int) time(NULL));
 q = random() % LARGE;
 /* test for even number */
 if ( q & 0x01 == 0 ) continue;
 if(MillerRobinTest(q, MAX_ITERATION))
break;
}

long int g=primitiveroot(q);
printf("%ld %ld\n",q,g);
long int i;
creatematrix_G(g,q);
creatematrix_D();
 //long int *temp[LAMDA+1],i;
   // for (i=0; i<n; i++)
       //  temp[i] = (long int *)malloc(n * sizeof(long int));
long int temp[600][600];
long int A[600][LAMDA+1];
//long int *A[n];
//for (i=0; i<n; i++)
        // A[i] = (long int *)malloc((LAMDA+5) * sizeof(long int));
long int c,d,k,sum=0,x;
//printf("good to go");
for (c = 0; c < LAMDA+1; c++) {
      for (d = 0; d <n; d++) {
        for (k = 0; k < LAMDA+1; k++) {
          sum = sum + D[c][k]*G[k][d];
        }
 
        temp[c][d] = sum;
        sum = 0;
      }
    }
 for (c = 0; c <LAMDA+1; c++) 
      for (d = 0; d <n; d++) 
         A[d][c]=temp[c][d];
        
for (c = 0; c <n; c++) {
      for (d = 0; d <n; d++) {
        for (k = 0; k < LAMDA+1; k++) {
  sum = sum + A[c][k]*G[k][d];
        }
 
        temp[c][d] = sum;
        sum = 0;
      }
    }
//printf("hello");
FILE *ptr_file;
	

		ptr_file =fopen("key.txt", "w");

		if (!ptr_file)
			printf("no file");
  int neighbour;          
for (i = 0; i < n; ++i)
	{
              fprintf(ptr_file, "NODE: %ld :NL={", i);
		
        
        int phy_neighbours_size=sensor_node[i].phynbrsize;
        for(x=0; x<phy_neighbours_size; ++x)
    	{
           //printf("%d",*(sensor_node[i].phynbr+x));
            neighbour=*(sensor_node[i].phynbr+x);
            //fprintf(ptr_file, "phy_neighbours :    ");
           fprintf(ptr_file, " %d ",neighbour);
           //printf("%d", *(sensor_node[i].phynbr+x));
            
          //fprintf(ptr_file,"%s"," ");
        }
         fprintf(ptr_file," }");
         fprintf(ptr_file," \n");
            
        for(x=0; x<phy_neighbours_size; ++x)
    	{
           neighbour=*(sensor_node[i].phynbr+x);
                long int key=temp[i][neighbour];
               fprintf(ptr_file, "key of (%ld,%d):",i,neighbour);
             fprintf(ptr_file, " %ld , ",key);
            //fprintf(ptr_file,"%ld", temp[i][neighbour]);
            
          
        }
fprintf(ptr_file," \n");
fprintf(ptr_file," \n");
 //fclose(ptr_file);
}
fclose(ptr_file);

return 0;
}
