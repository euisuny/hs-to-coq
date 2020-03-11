#include <stdlib.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <stdio.h>

#define BUFFER_SIZE 128
#define INVALID_SOCKET -1

typedef int socket_fd;

int main(int argc, char** argv) {
  
  int sock;
  struct sockaddr_in server;
  char message[BUFFER_SIZE] , server_reply[BUFFER_SIZE];

  //Create socket
  sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock == -1)
    {
      printf("Could not create socket\n");
    }
  printf("Socket created\n");

  server.sin_addr.s_addr = inet_addr("127.0.0.1");
  server.sin_family = AF_INET;
  server.sin_port = htons(argc > 2 ? atoi(argv[1]) : 8000);

  //Connect to remote server
  if (connect(sock , (struct sockaddr * )&server , sizeof(server)) < 0)
    {
      perror("connect failed. Error");
      return 1;
    }

  printf("Connected\n");

  //keep communicating with server
  int i;
  for (i = 0; i < 10; i++)
    {
      if (i % 2 == 0) {
	memset (message, 'a', BUFFER_SIZE);
      }
      else {
	memset (message, 'b', BUFFER_SIZE);
      }

      message[BUFFER_SIZE - 1] = '\0';

      memset (server_reply, 0, BUFFER_SIZE);

      int j;
      for (j = 0; j < BUFFER_SIZE; j += 8) {
	if( send(sock , message + j , 8 , 0) < 0)
	{
	  printf("Send failed");
	  return 1;
	}
	printf("Sent\n");
      } 
      
      //Receive a reply from the server
      if( recv(sock , server_reply , BUFFER_SIZE , 0) < 0)
	{
	  printf("recv failed");
	  break;
        }

      printf("Received\n");

      printf("Server reply :");
      printf("%s\n", server_reply);

    }

    return 0;
}
