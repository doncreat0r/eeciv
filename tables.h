

#ifndef TABLES_H
#define TABLES_H

// Default PID Map, same as FDS/WDS for now (v4)
// TODO: Reorganize for accurate fuel consumption calc
u08 PROGMEM PIDMap[0x10*8]  = {
		0x01,0x38, 0x11,0x28, 0x09,0xB8, 0x0D,0xF8,	// 0: N(RPM), VBAT, ITP(TPS), LAMBSE1
		0x0E,0xC8, 0x06,0x48, 0x10,0x38, 0x05,0x78,	// 1: APT, IECT, ECT, IACT
		0x0F,0xD8, 0x15,0x68, 0x26,0x68, 0x07,0x58,	// 2: ACT, ISCDTY, not used (MAF), IEGR
		0x0C,0xE8, 0x04,0x68, 0x08,0xA8, 0x0B,0x98,	// 3: FUELPW1, SAFTOT, IEGO1, IVCAL
		0x17,0x48, 0x1A,0x98, 0x1B,0x88, 0x16,0x58,	// 4: VSBAR, BITMAP_0, BITMAP_1, not used
		0x02,0x08, 0x03,0x18, 0x12,0x18, 0x0A,0x88,	// 5: +++ MAP, BP, MAP_FREQ, N/U 0A
		0x13,0x08, 0x18,0xB8, 0x19,0xA8, 0x1C,0xF8,	// 6: EGRDC, VS, N/U 19, N/U 1C
		0x27,0x78, 0x28,0x88, 0x2A,0xA8, 0x2B,0xB8,	// 7: LOAD, KAMRF1, DSDRPM, RATCH
		0x01,0x38, 0x11,0x28, 0x09,0xB8, 0x0D,0xF8,	// 8:
		0x0E,0xC8, 0x06,0x48, 0x10,0x38, 0x05,0x78,	// 9:
		0x0F,0xD8, 0x15,0x68, 0x26,0x68, 0x07,0x58,	// A:
		0x0C,0xE8, 0x04,0x68, 0x08,0xA8, 0x0B,0x98,	// B:
		0x35,0x48, 0x36,0x78, 0x37,0x68, 0x38,0x98,	// C: ETVOCM, TV_PRES, ITOT, PDL
		0x2D,0xD8, 0x2E,0xE8, 0x2F,0xF8, 0x30,0x18,	// D: ATMR1, IOCC, INDS, BCSDC
		0x32,0x38, 0x18,0xB8, 0x24,0x48, 0x25,0x58,	// E: GR_CM, VS, FMEM_FLAGS, FMEM_FLAG2
		0x27,0x78, 0x28,0x88, 0x2A,0xA8, 0x2B,0xB8};// F: LOAD, KAMRF1, DSDRPM, RATCH

u08 PROGMEM PIDMapT[0x10*8]  = {
		0x0A,0x38, 0x14,0x28, 0x16,0xB8, 0x19,0xF8,	// 0: 
		0x1C,0xC8, 0x1D,0x48, 0x24,0x38, 0x25,0x78,	// 1: 
		0x26,0xD8, 0x29,0x68, 0x2C,0x68, 0x31,0x58,	// 2: 
		0x33,0xE8, 0x34,0x68, 0x39,0xA8, 0x3A,0x98,	// 3: 
		0x3B,0x48, 0x3C,0x98, 0x3D,0x88, 0x3E,0x58,	// 4: 
		0x3F,0x08, 0x40,0x18, 0x41,0x18, 0x42,0x88,	// 5: 
		0x43,0x08, 0x44,0xB8, 0x45,0xA8, 0x46,0xF8,	// 6: 
		0x47,0x78, 0x48,0x88, 0x49,0xA8, 0x4A,0xB8,	// 7: 
		0x4B,0x38, 0x4C,0x28, 0x4D,0xB8, 0x4E,0xF8,	// 8:
		0x4F,0xC8, 0x50,0x48, 0x51,0x38, 0x52,0x78,	// 9:
		0x53,0xD8, 0x54,0x68, 0x55,0x68, 0x56,0x58,	// A:
		0x57,0xE8, 0x58,0x68, 0x59,0xA8, 0x5A,0x98,	// B:
		0x5B,0x48, 0x5C,0x78, 0x5D,0x68, 0x5E,0x98,	// C: 
		0x5F,0xD8, 0x60,0xE8, 0x61,0xF8, 0x62,0x18,	// D: 
		0x63,0x38, 0x64,0xB8, 0x65,0x48, 0x66,0x58,	// E: 
		0x67,0x78, 0x68,0x88, 0x69,0xA8, 0x6A,0xB8};// F: 

u08 PROGMEM DMRMap[0x10*8]  = {
//		0x00,0x00, 0x01,0x00, 0x02,0x00, 0x03,0x00,	// 0: 
//		0x04,0x00, 0x05,0x00, 0x06,0x00, 0x07,0x00,	// 1: 
//		0x08,0x00, 0x09,0x00, 0x0A,0x00, 0x0B,0x00,	// 2: 
//		0x0C,0x00, 0x0D,0x00, 0x0E,0x00, 0x0F,0x00,	// 3: 
		0x10,0x00, 0x11,0x00, 0x12,0x00, 0x13,0x00,	// 4: 
		0x14,0x00, 0x15,0x00, 0x16,0x00, 0x17,0x00,	// 5: 
		0x18,0x00, 0x19,0x00, 0x1A,0x00, 0x1B,0x00,	// 6: 
		0x1C,0x00, 0x1D,0x00, 0x1E,0x00, 0x1F,0x00,	// 7: 
		0x20,0x00, 0x21,0x00, 0x22,0x00, 0x23,0x00,	// 8: 
		0x24,0x00, 0x25,0x00, 0x26,0x00, 0x27,0x00,	// 9: 
		0x28,0x00, 0x29,0x00, 0x2A,0x00, 0x2B,0x00,	// A: 
		0x2C,0x00, 0x2D,0x00, 0x2E,0x00, 0x2F,0x00,	// B: 
		0x30,0x00, 0x31,0x00, 0x32,0x00, 0x33,0x00,	// C: 
		0x34,0x00, 0x35,0x00, 0x36,0x00, 0x37,0x00,	// D: 
		0x38,0x00, 0x39,0x00, 0x3A,0x00, 0x3B,0x00,	// E: 
		0x3C,0x00, 0x3D,0x00, 0x3E,0x00, 0x3F,0x00,	// F: 
		0x40,0x00, 0x41,0x00, 0x42,0x00, 0x43,0x00,	// D: 
		0x44,0x00, 0x45,0x00, 0x46,0x00, 0x47,0x00,	// E: 
		0x48,0x00, 0x49,0x00, 0x4A,0x00, 0x4B,0x00,	// F: 
		0x4C,0x00, 0x4D,0x00, 0x4E,0x00, 0x4F,0x00};// F:

u08 PROGMEM BaudMap[0x10*8]  = {
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 0: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 1: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 2: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 3: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 4: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 5: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 6: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 7: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 4: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 5: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 6: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 7: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 4: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 5: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00,	// 6: 
		0x00,0x00, 0x00,0x00, 0x00,0x00, 0x00,0x00};


volatile u08 cmdBuf[0x10][28] = 
		{{0x01, 0xB0, 0x00, 0x00, 0x00, 0x00}, 
		 {0xFF, 0x5F, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0xA0, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 
		 {0x00, 0x00, 0x00, 0x00, 0x00, 0x00}};		// command to feed main buffer

volatile u08 cmdData[19][2] = {		// commands map: index = CMDChar - 0x41 ( +0x20 to get the wait for resp code)
			{0x03, 0x81}, 			// 'A' - get status
			{0x26, 0x0E},			// 'B' - read codes
			{0x02, 0x91},			// 'C' - clear codes
			{0x25, 0x3E},			// 'D' - run KOEO/KOER

			{0x41, 0x96},			// 'E' - transmit PID map (update 2nd byte with frame length & VP!!!)
			{0x00, 0x5E},			// 'F' - read PID map - 0x23
			{0x21, 0xF6},			// 'G' - read PID values

			{0x01, 0xA1},			// 'H' - clear DCL error/flag register

			{0x42, 0xA6},			// 'I' - transmit DMR map
			{0x24, 0x2E},			// 'J' - read DMR map
			{0x22, 0xC6},			// 'K' - read DMR values

			{0x27, 0x1E},			// 'L' - read both PID/DMR values
			{0x81, 0x74},			// 'M' - switch to another baudrate (BR const in baudConst)
			{0x00, 0x00},			// 'N'
			{0x00, 0x00},			// 'O'
			{0x00, 0x00},			// 'P'
			{0x41, 0x1E},			// 'Q' - zero command - switch to this mode to stop the PID values flow
			{0xFF, 0x5F}			// 'R' - idle block - repeat the PID list last time, than switch to no cmd
		};

// Options map
#define optDefaultBaudrate	0
#define optCartHex			1

// ======================================================
#define NIB2BYTE(x) ((x > 0x40)?((x-55)&0x0F):((x-48)&0x0F))
// ======================================================
// assume new command in CMD buffer, x - low byte, y - high byte which receives VP nibble
#define VPARITY(x, y) ( (((x & 0x0F) ^ ((x>>4) & 0x0F) ^ (y & 0x0F) ^ 0x0A) << 4) | (y & 0x0F))

// ======================================================
// Recalc VP on cmdBuf
void RecalcCmdBufVP()
{
	u08 i, j;
	for (i=0;i<16;i++)
	{
		for (j=3;j<28;j++)
		{
			cmdBuf[i][j] = VPARITY(cmdBuf[i][j-1], cmdBuf[i][j]); // 0xA0;
			j++;
		}
	}
}

// ======================================================
// Copy from Default PID Map to cmdBuf
void InitDefaultPIDMap()
{
	u08 i, j;
	for (i=0;i<16;i++)
		for (j=0;j<8;j++)
			cmdBuf[i][j+2] = pgm_read_byte(&PIDMap[i*8+j]);
	RecalcCmdBufVP();
}

void InitTestPIDMap()
{
	u08 i, j;
	for (i=0;i<16;i++)
		for (j=0;j<8;j++)
			cmdBuf[i][j+2] = pgm_read_byte(&PIDMapT[i*8+j]);
	RecalcCmdBufVP();
}

// ======================================================
// DEMO Copy from Default PID Map to cmdBuf
void InitDemoPIDMap()
{
	u08 i, j;
	for (j=0;j<8;j++)
		cmdBuf[0][j+2] = pgm_read_byte(&PIDMap[j]);
	for (i=1;i<16;i++)
		for (j=0;j<8;j++)
			cmdBuf[i][j+2] = 0x00;
	RecalcCmdBufVP();
}

// ======================================================
// Copy from Default DMR Map to cmdBuf
void InitDefaultDMRMap()
{
	u08 i, j;
	for (i=0;i<16;i++)
		for (j=0;j<8;j++)
			cmdBuf[i][j+2] = pgm_read_byte(&DMRMap[i*8+j]);
	RecalcCmdBufVP();
}

// ======================================================
// Copy from Default DMR Map to cmdBuf
void InitDefaultBaudMap()
{
	u08 i, j;
	for (i=0;i<16;i++)
		for (j=0;j<8;j++)
			cmdBuf[i][j+2] = pgm_read_byte(&BaudMap[i*8+j]);
//	RecalcCmdBufVP();
}

void SetQualifier(u08 b1, u08 b2, u08 b3)
{
	cmdBuf[3][0] = (NIB2BYTE(b3) | (NIB2BYTE(b2)<<4));    // minus 0x10 in offset map
	if (cmdBuf[3][0]) {
		cmdBuf[3][0]--;
		cmdBuf[3][1] = VPARITY(cmdBuf[3][0], NIB2BYTE(b1));
	} else {
		// VP
		cmdBuf[3][0]--;
		cmdBuf[3][1] = VPARITY(cmdBuf[3][0], ((NIB2BYTE(b1))-1));
	}
}

#endif
