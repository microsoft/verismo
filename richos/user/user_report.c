#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include "report.h"

int main(int arg, char ** argv){
        if(arg != 2){
		printf("Provide a input attestation file\n");
		return -1;
	}
	struct msg_report_resp report;
	char * filename = argv[1];
	FILE* fp = fopen(filename, "rb");
	fread(&report, sizeof(report), 1, fp);
	print_report(&report);
	fclose(fp);
	return 0;
}