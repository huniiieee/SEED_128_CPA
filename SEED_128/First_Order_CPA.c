
// First_Order_CPA.c
//

#include "Analysis.h"
#include "Table.h"

unsigned int G_fun(unsigned int x) {

	unsigned char y[4] = { 0, };
	unsigned char z[4] = { 0, };
	unsigned char m[4] = { 0xfc, 0xf3, 0xcf, 0x3f };


	y[0] = SEED_S1[((x) & 0xff)];
	y[1] = SEED_S2[((x) >> 8) & 0xff];
	y[2] = SEED_S1[((x) >> 16) & 0xff];
	y[3] = SEED_S2[((x) >> 24) & 0xff];

	z[3] = (y[0] & m[3]) ^ (y[1] & m[0]) ^ (y[2] & m[1]) ^ (y[3] & m[2]); // 0x3f 0xfc 0xf3 0xcf
	z[2] = (y[0] & m[2]) ^ (y[1] & m[3]) ^ (y[2] & m[0]) ^ (y[3] & m[1]); // 0xcf 0x3f 0xfc 0xf3
	z[1] = (y[0] & m[1]) ^ (y[1] & m[2]) ^ (y[2] & m[3]) ^ (y[3] & m[0]); // 0xf3 0xcf 0x3f 0xfc 
	z[0] = (y[0] & m[0]) ^ (y[1] & m[1]) ^ (y[2] & m[2]) ^ (y[3] & m[3]); // 0xfc 0xf3 0xcf 0x3f

	return (z[0] | (z[1] << 8) | (z[2] << 16) | (z[3] << 24));
}

void F_fun(unsigned int C, unsigned int D, unsigned int K0, unsigned int K1, unsigned int* E, unsigned int* F) {

	unsigned int First = 0;
	unsigned int Second = 0;

	First = (C ^ K0) ^ (D ^ K1);
	First = G_fun(First);
	Second = First;
	First = (First + (C ^ K0)) & 0xffffffff;
	First = G_fun(First);
	Second = (Second + First) & 0xffffffff;
	Second = G_fun(Second);
	*F = Second;
	*E = (First + Second) & 0xffffffff;

}

//바이트 배열과 값이 같은 워드 생성
unsigned int BtW(unsigned char plain[4])
{
	unsigned text = 0;
	for (int i = 0; i < 4; i++)
		text += (unsigned int)plain[i] << (8 * i);
	return text;
}

//워드와 값이 같은 바이트배열 생성
void WtB(unsigned text, unsigned char cipher[4])
{
	for (int i = 0; i < 4; i++)
		cipher[i] = (text >> (8 * i)) & 0xff;
}

int First_Order_CPA(struct tm* TIME, unsigned int POINTS, unsigned int TRACE_NUM)
{
	/************************************************************************************/
	/*                                     변수 선언                                    */
	/************************************************************************************/
	FILE* fp = NULL;
	FILE* fp2 = NULL;
	FILE* fpp = NULL;
	FILE* fpt = NULL;

	char			FOLD_MERGE[_FILE_NAME_SIZE_] = "";
	char			FILE_MERGE[_FILE_NAME_SIZE_] = "";

	unsigned char* Plaintext = NULL;


	unsigned int	i = 0;		// for (_BLOCK_SIZE, _CANDIDATES_)
	unsigned int	B = 0;		// Byte
	unsigned int	R = 0;
	unsigned int	Guess_Key = 0;
	unsigned int	Key = 0;
	unsigned int	Key_HW = 0;
	unsigned int	R_Key = 0;
	unsigned int	Right_Key = 0;
	unsigned int	Index = 0;
	unsigned int	Percent = 0;
	unsigned int	Check = 0;
	unsigned int	temp = 0;
	unsigned int	Key1[2] = { 0, };
	unsigned int	Key0[2] = { 0, };

	unsigned int	input32 = 0;
	unsigned int	Plain = 0;
	unsigned int	C = 0;
	unsigned int	D = 0;

	__int64* H_S = NULL;
	__int64* H_SS = NULL;
	__int64			tn = 0;		// for (TN)
	__int64			pi = 0;		// for (PI)
	__int64			TN = 0;		// Trace Number
	__int64			PI = 0;		// Point Interval

	float			F_Temp = 0.;

	double* Temp_Points = NULL;
	double* MaxPeak = NULL;
	double* W_CS = NULL;
	double* W_CSS = NULL;
	double** W_HS = NULL;
	unsigned char* Key_Xor = NULL;
	unsigned char* input = NULL;

	
	double			Correlation = 0.;
	double			Correlation_L = 0.;
	double			Correlation_R = 0.;
	double			Max = 0.;
	double			Max_Sec = 0.;
	double			Ratio = 0.;

	// 분석할 파형 및 포인트 수 계산
	TN = (__int64)_TRACE_NUM_;
	PI = (__int64)_END_POINT_ - (__int64)_START_POINT_ + (__int64)1;


	/************************************************************************************/
	/*                              변수 설정 값 오류 검사                              */
	/************************************************************************************/
	if (TRACE_NUM < TN) {
		printf(" -----------------------------------------------------------------------\n");
		printf("|                    분석 파형 수가 적절치 않습니다.                    |\n");
		printf(" -----------------------------------------------------------------------\n");
		return _FAIL_;
	}

	if (_START_POINT_ < 1 || _START_POINT_ > _END_POINT_) {
		printf(" -----------------------------------------------------------------------\n");
		printf("|                분석 범위의 시작 지점이 적절치 않습니다.               |\n");
		printf(" -----------------------------------------------------------------------\n");
		return _FAIL_;
	}

	if (_END_POINT_ > POINTS) {
		printf(" -----------------------------------------------------------------------\n");
		printf("|                 분석 범위의 끝 지점이 적절치 않습니다.                |\n");
		printf(" -----------------------------------------------------------------------\n");
		return _FAIL_;
	}

	/************************************************************************************/
	/*                                   변수 동적할당                                   /
	/************************************************************************************/
	// 평문 저장
	Plaintext = (unsigned char*)malloc(_BLOCK_SIZE_ * sizeof(unsigned char));

	// 분석 포인트 저장
	Temp_Points = (double*)malloc((unsigned int)PI * sizeof(double));

	// 중간값 E[X] 저장
	H_S = (__int64*)malloc(_GUESS_KEY_NUM_ * sizeof(__int64));

	// 중간값 E[X^2] 저장
	H_SS = (__int64*)malloc(_GUESS_KEY_NUM_ * sizeof(__int64));

	// 파형 측정값 E[Y] 저장
	W_CS = (double*)malloc((unsigned int)PI * sizeof(double));

	// 파형 측정값 E[Y^2] 저장 
	W_CSS = (double*)malloc((unsigned int)PI * sizeof(double));

	// E[XY] 저장
	W_HS = (double**)malloc(_GUESS_KEY_NUM_ * sizeof(double*));
	for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
		W_HS[Guess_Key] = (double*)malloc((unsigned int)PI * sizeof(double));
	}

	// 각 키 후보군 별 MAXPEAK 저장
	MaxPeak = (double*)malloc(_GUESS_KEY_NUM_ * sizeof(double));

	//라운드 키 반반씩 xor한 값 저장
	Key_Xor = (unsigned char*)malloc((_ROUND_KEY_SIZE_ / 2) * sizeof(unsigned char));

	//G함수 입력값 저장
	input = (unsigned char*)malloc((_ROUND_KEY_SIZE_ / 2) * sizeof(unsigned char));




	/************************************************************************************/
	/*                               First Order CPA 시작                               */
	/************************************************************************************/
	// 평문 파일 열기 (읽기 모드)
	sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%s.txt", _FOLD_, _PLAIN_FILE_);
	fopen_s(&fpp, FILE_MERGE, "r");
	if (fpp == NULL) {
		printf(" -----------------------------------------------------------------------\n");
		printf("|                        Failed To Read Plaintext                       |\n");
		printf(" -----------------------------------------------------------------------\n");
		return _FAIL_;
	}

	// 파형 파일 열기 (읽기 모드)
	sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%s.trace", _FOLD_, _TRACE_FILE_);
	fopen_s(&fpt, FILE_MERGE, "rb");
	if (fpt == NULL) {
		printf(" -----------------------------------------------------------------------\n");
		printf("|                          Failed To Read Trace                         |\n");
		printf(" -----------------------------------------------------------------------\n");
		return _FAIL_;
	}



	for (R = 0; R < 2; R++)
	{
#if 1
		// 결과 저장할 폴더 생성
		sprintf_s(FOLD_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%04d_%02d_%02d_%02d_%02d_%02d_%dRound", _FOLD_, TIME->tm_year + 1900, TIME->tm_mon + 1, TIME->tm_mday, TIME->tm_hour, TIME->tm_min, TIME->tm_sec,R+1);
		_mkdir(FOLD_MERGE);
		for (B = _START_BYTE_ - 1; B < _END_BYTE_; B++) {

			// 값 초기화
			for (pi = 0; pi < PI; pi++) {
				W_CS[pi] = 0.0;
				W_CSS[pi] = 0.0;
				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
					W_HS[Guess_Key][pi] = 0.0;
				}
			}
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
				MaxPeak[Guess_Key] = 0;
				H_S[Guess_Key] = 0;
				H_SS[Guess_Key] = 0;
			}

			printf(" -----------------------------------------------------------------------\n");
			printf("|                            Loading Trace...                           |\n");
			printf(" -----------------------------------------------------------------------\n");


			for (tn = 0; tn < TN; tn++) {
				// 진행률 표시
				Percent = (unsigned int)((double)tn / (double)TN * 100);
				if (Percent % 10 == 0 && Percent != 0 && Check != Percent) {
					printf("%d%%\t", Percent);
					if (Percent == 90) {
						printf("\n");
					}
					Check = Percent;
				}

				// 평문 불러오기 (1라운드)
				if (R == 0)
				{
					_fseeki64(fpp, ((__int64)_BLOCK_SIZE_ * (__int64)3 + (__int64)2) * (__int64)tn, SEEK_SET);
					for (i = 0; i < _BLOCK_SIZE_; i++) {
						fscanf_s(fpp, "%hhx", &Plaintext[i]);
					}
				}

				//평문 불러오기 (2라운드)
				else
				{
					_fseeki64(fpp, ((__int64)_BLOCK_SIZE_ * (__int64)3 + (__int64)2) * (__int64)tn, SEEK_SET);
					for (i = 0; i < _BLOCK_SIZE_; i++) {
						fscanf_s(fpp, "%hhx", &Plaintext[i]);
					}

					C = BtW(&Plaintext[8]);
					D = BtW(&Plaintext[12]);
					F_fun(C, D, Key0[0], Key1[0], &C, &D);
					WtB(C, &Plaintext[8]);
					WtB(D, &Plaintext[12]);
					for (i = 0; i < 8; i++)
					{
						Plaintext[8 + i] ^= Plaintext[i];
					}

				}

				// 포인트 값 불러오기
				_fseeki64(fpt, 32 + ((__int64)POINTS * (__int64)tn + (__int64)_START_POINT_ - (__int64)1) * (__int64)4, SEEK_SET);
				for (pi = 0; pi < PI; pi++) {
					fread(&F_Temp, sizeof(float), 1, fpt);
					Temp_Points[pi] = (double)F_Temp;
				}

				// E[Y], E[Y^2] 계산
				for (pi = 0; pi < PI; pi++) {
					W_CS[pi] += Temp_Points[pi];
					W_CSS[pi] += Temp_Points[pi] * Temp_Points[pi];
				}

				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {

					if (B % 2)
						Key = SEED_S2[Plaintext[8 + B] ^ Plaintext[12 + B] ^ (Guess_Key + _GUESS_KEY_START_)];
					else
						Key = SEED_S1[Plaintext[8 + B] ^ Plaintext[12 + B] ^ (Guess_Key + _GUESS_KEY_START_)];

					// Hamming Weight 계산
					Key_HW = (Key & 1) + ((Key >> 1) & 1) + ((Key >> 2) & 1) + ((Key >> 3) & 1) + ((Key >> 4) & 1) + ((Key >> 5) & 1) + ((Key >> 6) & 1) + ((Key >> 7) & 1);

					// E[X], E[X^2] 계산
					H_S[Guess_Key] += (__int64)Key_HW;
					H_SS[Guess_Key] += (__int64)(Key_HW * Key_HW);

					// E[XY] 계산
					for (pi = 0; pi < PI; pi++) {
						W_HS[Guess_Key][pi] += (double)Key_HW * Temp_Points[pi];
					}
				}

#if _MAX_PEAK_TRACE_
				// Max Peak Trace 저장
				if (!((tn + 1) % _TRACE_UNIT_)) {
					// Max Peak Trace 저장할 파일 열기
					sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_MAX_PEAK_UNIT_%d.txt", FOLD_MERGE, B + 1, _TRACE_UNIT_);
					fopen_s(&fp, FILE_MERGE, "a");

					for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
						for (pi = 0; pi < PI; pi++) {
							Correlation_L = (double)(tn + 1) * W_HS[Guess_Key][pi] - W_CS[pi] * (double)H_S[Guess_Key];
							Correlation_R = ((double)(tn + 1) * (double)H_SS[Guess_Key] - (double)H_S[Guess_Key] * (double)H_S[Guess_Key]) * ((double)(tn + 1) * W_CSS[pi] - W_CS[pi] * W_CS[pi]);

							if (Correlation_R <= (double)0) {
								Correlation = (double)0;
							}
							else {
								Correlation = Correlation_L / sqrt(Correlation_R);
								Correlation = fabs(Correlation);
							}

							if (MaxPeak[Guess_Key] < Correlation) {
								MaxPeak[Guess_Key] = Correlation;
							}
						}

						fprintf_s(fp, "%f ", MaxPeak[Guess_Key]);
					}

					fprintf_s(fp, "\n");

					fclose(fp);

					// 값 초기화
					for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
						MaxPeak[Guess_Key] = 0;
					}
				}
#endif
			}

			printf(" -----------------------------------------------------------------------\n");
			printf("|              Correlation Power Analysis On Key Candidates             |\n");
			printf(" -----------------------------------------------------------------------\n");


#if _CORRELATION_TRACE_
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d", FOLD_MERGE, B + 1);
			_mkdir(FILE_MERGE);
#endif

			// 키에 대한 상관계수 계산 및 결과 값 저장
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
#if _CORRELATION_TRACE_
				sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d\\%03d(0x%02X).txt", FOLD_MERGE, B + 1, Guess_Key + _GUESS_KEY_START_, Guess_Key + _GUESS_KEY_START_);
				fopen_s(&fp, FILE_MERGE, "w");
#endif

				for (pi = 0; pi < PI; pi++) {
					Correlation_L = (double)TN * W_HS[Guess_Key][pi] - W_CS[pi] * (double)H_S[Guess_Key];
					Correlation_R = ((double)TN * (double)H_SS[Guess_Key] - (double)H_S[Guess_Key] * (double)H_S[Guess_Key]) * ((double)TN * W_CSS[pi] - W_CS[pi] * W_CS[pi]);
					//printf("%f", Correlation_R);
					if (Correlation_R <= (double)0) {
						Correlation = (double)0;
					}
					else {
						Correlation = Correlation_L / sqrt(Correlation_R);
						Correlation = fabs(Correlation);
					}

#if _CORRELATION_TRACE_
					fprintf_s(fp, "%f\n", Correlation);
#endif

					if (MaxPeak[Guess_Key] < Correlation) {
						MaxPeak[Guess_Key] = Correlation;

#if _GUESS_KEY_NUM_ == 1
						// 최종 분석 결과 저장
						Index = (unsigned int)pi;

						sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_Result.txt", FOLD_MERGE, B + 1);
						fopen_s(&fp2, FILE_MERGE, "w");

						fprintf_s(fp2, "Point		: %d\n", Index + _START_POINT_);
						fprintf_s(fp2, "Correlation	: %f", MaxPeak[Guess_Key]);

						fclose(fp2);
#endif
					}
				}

#if _CORRELATION_TRACE_
				fclose(fp);
#endif
			}

#if _GUESS_KEY_NUM_ > 1
			// Guess Key Peak 저장
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_GUESS_KEY_PEAK.txt", FOLD_MERGE, B + 1);
			fopen_s(&fp, FILE_MERGE, "w");

			// 최종 분석 키 저장
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_RIGHT_KEY.txt", FOLD_MERGE, B + 1);
			fopen_s(&fp2, FILE_MERGE, "w");

			Max = 0;
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
				fprintf_s(fp, "%f\n", MaxPeak[Guess_Key]);

				if (Max < MaxPeak[Guess_Key]) {
					Max = MaxPeak[Guess_Key];
					R_Key = Guess_Key;
				}
			}

			Key_Xor[B] = R_Key;

			fclose(fp);

			fprintf_s(fp2, "  1st  0x%02X  %f\n", R_Key, Max);


			MaxPeak[R_Key] = 0.0;

			for (i = 1; i < _CANDIDATES_; i++) {
				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
					if (Max_Sec < MaxPeak[Guess_Key]) {
						Max_Sec = MaxPeak[Guess_Key];
						Right_Key = Guess_Key;
					}
				}

				if (i == 1) {
					fprintf_s(fp2, "  2nd  0x%02X  %f\n", Right_Key, Max_Sec);
					Ratio = Max / Max_Sec;
				}
				else if (i == 2) {
					fprintf_s(fp2, "  3rd  0x%02X  %f\n", Right_Key, Max_Sec);
				}
				else {
					fprintf_s(fp2, "%3dth  0x%02X  %f\n", i + 1, Right_Key, Max_Sec);
				}

				MaxPeak[Right_Key] = 0.0;
				Max_Sec = 0.0;
				Right_Key = 0;
			}

			fprintf_s(fp2, "\nRatio  %f\n", Ratio);

			fclose(fp2);



#endif
		}
		//Key_left
#endif

#if 1

		for (B = _START_BYTE_ - 1; B < _END_BYTE_; B++) {

			// 값 초기화
			for (pi = 0; pi < PI; pi++) {
				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
					W_HS[Guess_Key][pi] = 0.0;
				}
			}
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
				MaxPeak[Guess_Key] = 0;
				H_S[Guess_Key] = 0;
				H_SS[Guess_Key] = 0;
			}

			printf(" -----------------------------------------------------------------------\n");
			printf("|                            Loading Trace...                           |\n");
			printf(" -----------------------------------------------------------------------\n");


			for (tn = 0; tn < TN; tn++) {
				// 진행률 표시
				Percent = (unsigned int)((double)tn / (double)TN * 100);
				if (Percent % 10 == 0 && Percent != 0 && Check != Percent) {
					printf("%d%%\t", Percent);
					if (Percent == 90) {
						printf("\n");
					}
					Check = Percent;
				}

				// 평문 불러오기 (1라운드)
				if (R == 0)
				{
					_fseeki64(fpp, ((__int64)_BLOCK_SIZE_ * (__int64)3 + (__int64)2) * (__int64)tn, SEEK_SET);
					for (i = 0; i < _BLOCK_SIZE_; i++) {
						fscanf_s(fpp, "%hhx", &Plaintext[i]);
					}
				}

				//평문 불러오기 (2라운드)
				else
				{
					_fseeki64(fpp, ((__int64)_BLOCK_SIZE_ * (__int64)3 + (__int64)2) * (__int64)tn, SEEK_SET);
					for (i = 0; i < _BLOCK_SIZE_; i++) {
						fscanf_s(fpp, "%hhx", &Plaintext[i]);
					}

					C = BtW(&Plaintext[8]);
					D = BtW(&Plaintext[12]);
					F_fun(C, D, Key0[0], Key1[0], &C, &D);
					WtB(C, &Plaintext[8]);
					WtB(D, &Plaintext[12]);
					for (i = 0; i < 8; i++)
					{
						Plaintext[8 + i] ^= Plaintext[i];
					}

				}

				// 포인트 값 불러오기
				_fseeki64(fpt, 32 + ((__int64)POINTS * (__int64)tn + (__int64)_START_POINT_ - (__int64)1) * (__int64)4, SEEK_SET);
				for (pi = 0; pi < PI; pi++) {
					fread(&F_Temp, sizeof(float), 1, fpt);
					Temp_Points[pi] = (double)F_Temp;
				}

				for (int i = 0; i < _ROUND_KEY_SIZE_ / 2; i++)
					input[i] = Plaintext[8 + i] ^ Plaintext[12 + i] ^ Key_Xor[i];

				input32 = BtW(input);
				input32 = G_fun(input32);
				Plain = BtW(&Plaintext[8]);

				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {

					temp = Guess_Key << (8 * B);
					temp ^= Key0[R];
					if (B % 2)
						Key = SEED_S2[(unsigned char)(((Plain ^ temp) + input32) >> (8 * B))];
					else
						Key = SEED_S1[(unsigned char)(((Plain ^ temp) + input32) >> (8 * B))];

					// Hamming Weight 계산
					Key_HW = (Key & 1) + ((Key >> 1) & 1) + ((Key >> 2) & 1) + ((Key >> 3) & 1) + ((Key >> 4) & 1) + ((Key >> 5) & 1) + ((Key >> 6) & 1) + ((Key >> 7) & 1);

					// E[X], E[X^2] 계산
					H_S[Guess_Key] += (__int64)Key_HW;
					H_SS[Guess_Key] += (__int64)(Key_HW * Key_HW);

					// E[XY] 계산
					for (pi = 0; pi < PI; pi++) {
						W_HS[Guess_Key][pi] += (double)Key_HW * Temp_Points[pi];
					}
				}

#if _MAX_PEAK_TRACE_
				// Max Peak Trace 저장
				if (!((tn + 1) % _TRACE_UNIT_)) {
					// Max Peak Trace 저장할 파일 열기
					sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_MAX_PEAK_UNIT_%d.txt", FOLD_MERGE, B + 1, _TRACE_UNIT_);
					fopen_s(&fp, FILE_MERGE, "a");

					for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
						for (pi = 0; pi < PI; pi++) {
							Correlation_L = (double)(tn + 1) * W_HS[Guess_Key][pi] - W_CS[pi] * (double)H_S[Guess_Key];
							Correlation_R = ((double)(tn + 1) * (double)H_SS[Guess_Key] - (double)H_S[Guess_Key] * (double)H_S[Guess_Key]) * ((double)(tn + 1) * W_CSS[pi] - W_CS[pi] * W_CS[pi]);

							if (Correlation_R <= (double)0) {
								Correlation = (double)0;
							}
							else {
								Correlation = Correlation_L / sqrt(Correlation_R);
								Correlation = fabs(Correlation);
							}

							if (MaxPeak[Guess_Key] < Correlation) {
								MaxPeak[Guess_Key] = Correlation;
							}
						}

						fprintf_s(fp, "%f ", MaxPeak[Guess_Key]);
					}

					fprintf_s(fp, "\n");

					fclose(fp);

					// 값 초기화
					for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
						MaxPeak[Guess_Key] = 0;
					}
				}
#endif
			}


			printf(" -----------------------------------------------------------------------\n");
			printf("|              Correlation Power Analysis On Key Candidates             |\n");
			printf(" -----------------------------------------------------------------------\n");


#if _CORRELATION_TRACE_
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_K0", FOLD_MERGE, B + 1);
			_mkdir(FILE_MERGE);
#endif

			// 키에 대한 상관계수 계산 및 결과 값 저장
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
#if _CORRELATION_TRACE_
				sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_K0\\%03d(0x%02X).txt", FOLD_MERGE, B + 1, Guess_Key + _GUESS_KEY_START_, Guess_Key + _GUESS_KEY_START_);
				fopen_s(&fp, FILE_MERGE, "w");
#endif

				for (pi = 0; pi < PI; pi++) {
					Correlation_L = (double)TN * W_HS[Guess_Key][pi] - W_CS[pi] * (double)H_S[Guess_Key];
					Correlation_R = ((double)TN * (double)H_SS[Guess_Key] - (double)H_S[Guess_Key] * (double)H_S[Guess_Key]) * ((double)TN * W_CSS[pi] - W_CS[pi] * W_CS[pi]);
					//printf("%f", Correlation_R);
					if (Correlation_R <= (double)0) {
						Correlation = (double)0;
					}
					else {
						Correlation = Correlation_L / sqrt(Correlation_R);
						Correlation = fabs(Correlation);
					}

#if _CORRELATION_TRACE_
					fprintf_s(fp, "%f\n", Correlation);
#endif

					if (MaxPeak[Guess_Key] < Correlation) {
						MaxPeak[Guess_Key] = Correlation;

#if _GUESS_KEY_NUM_ == 1
						// 최종 분석 결과 저장
						Index = (unsigned int)pi;

						sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_Result.txt", FOLD_MERGE, B + 1);
						fopen_s(&fp2, FILE_MERGE, "w");

						fprintf_s(fp2, "Point		: %d\n", Index + _START_POINT_);
						fprintf_s(fp2, "Correlation	: %f", MaxPeak[Guess_Key]);

						fclose(fp2);
#endif
					}
				}

#if _CORRELATION_TRACE_
				fclose(fp);
#endif
			}

#if _GUESS_KEY_NUM_ > 1


			// Guess Key Peak 저장
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_K0_GUESS_KEY_PEAK.txt", FOLD_MERGE, B + 1);
			fopen_s(&fp, FILE_MERGE, "w");

			// 최종 분석 키 저장
			sprintf_s(FILE_MERGE, _FILE_NAME_SIZE_ * sizeof(char), "%s\\%d_K0_RIGHT_KEY.txt", FOLD_MERGE, B + 1);
			fopen_s(&fp2, FILE_MERGE, "w");

			Max = 0;
			for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
				fprintf_s(fp, "%f\n", MaxPeak[Guess_Key]);

				if (Max < MaxPeak[Guess_Key]) {
					Max = MaxPeak[Guess_Key];
					R_Key = Guess_Key;
				}
			}

			Key0[R] ^= R_Key << (8 * B);

			fclose(fp);

			fprintf_s(fp2, "  1st  0x%02X  %f\n", R_Key, Max);


			MaxPeak[R_Key] = 0.0;

			for (i = 1; i < _CANDIDATES_; i++) {
				for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
					if (Max_Sec < MaxPeak[Guess_Key]) {
						Max_Sec = MaxPeak[Guess_Key];
						Right_Key = Guess_Key;
					}
				}

				if (i == 1) {
					fprintf_s(fp2, "  2nd  0x%02X  %f\n", Right_Key, Max_Sec);
					Ratio = Max / Max_Sec;
				}
				else if (i == 2) {
					fprintf_s(fp2, "  3rd  0x%02X  %f\n", Right_Key, Max_Sec);
				}
				else {
					fprintf_s(fp2, "%3dth  0x%02X  %f\n", i + 1, Right_Key, Max_Sec);
				}

				MaxPeak[Right_Key] = 0.0;
				Max_Sec = 0.0;
				Right_Key = 0;
			}

			fprintf_s(fp2, "\nRatio  %f\n", Ratio);

			fclose(fp2);



#endif
		}

		Key1[R] = Key0[R] ^ BtW(Key_Xor);
		printf("%d  Round K0 =%08x\n", R, Key0);
		printf("%d  Round K1 =%08x\n", R, Key1);
#endif
	}
	
	fclose(fpp);
	fclose(fpt);




	/************************************************************************************/
	/*                                  동적 할당 해제                                  */
	/************************************************************************************/
	free(Plaintext);
	free(Temp_Points);
	free(H_S);
	free(H_SS);
	free(W_CS);
	free(W_CSS);
	for (Guess_Key = 0; Guess_Key < _GUESS_KEY_NUM_; Guess_Key++) {
		free(W_HS[Guess_Key]);
	}
	free(W_HS);
	free(MaxPeak);
	free(Key_Xor);
	free(input);
	
	return _PASS_;
}
