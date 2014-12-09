// EEC-IV runtime and standby diagnostics, v4
// (c) Dmitry 'Creat0r' Bobrik, 2009-2015
// Now licensed under MIT Public License.
//
// Requirements:
// ATMega324P (or bigger with 2 UARTs), UART freq oscillator (11.0592 MHz or so)
// MAX485 (or similar) on UART1 - connect to pins 3, 11 of EEC-IV OBD2-style connector
// MAX232 (or similar) on UART0 - connect to PC COM port

// PROJECT TODO: 
// + 19200 comm + CART speed switch
// + auto CART speed (try 2400, 4800, 9600, 19200 in CART probe)
// + sleep modes!
// + clear pc buffer after receiving a command!!!

#define VER_RU
//#define VER_BY

#include <avr/io.h>
//#include <util/delay.h>
#include <avr/interrupt.h>
#include <avr/pgmspace.h>
#include <avr/wdt.h>
#include <avr/power.h>
#include <avr/eeprom.h>

#include "avrlibdefs.h"
#include "timer.h"
#include "tables.h"

#define INLINE __attribute__((inline))	// still doesn't work

#define modeNoMode	'u'					//
#define modeEchoID	'e'					//  start transmitting echo id
#define modeWaitID	'w'
#define modeGoCART	'g'
#define modeInCART	'c'
#define modeEchoSW	's'

#define brc38400 38400L						// used for PC comm
#define brd38400 (F_CPU/(brc38400*16L)-1)
#define brc19200 19200L						// 
#define brd19200 (F_CPU/(brc19200*16L)-1)		
#define brc9600 9600L						// CART mode EEC comm
#define brd9600 (F_CPU/(brc9600*16L)-1)		
#define brc4800 4800L						// 
#define brd4800 (F_CPU/(brc4800*16L)-1)		
#define brc2400 2400L						// UART mode EEC comm
#define brd2400 (F_CPU/(brc2400*16L)-1)     // +7

#define HI(x) ((x)>>8)
#define LO(x) ((x)& 0xFF)

#define PDDL	PD4							// data direction line for RS485 chip
#define PLED	PC3

// waiting for response code = (command code + 0x20)

// c - set pending specified code
#define cmdSetCode	'c'
// b - send buffer content
#define cmdSendBuf	'b'
// g - explicitly switch to CART mode, abandon current cmd
#define cmdSwCART	'g'
// r - reset MCU to bootloader
#define cmdReboot	'r'
// m - return current mode
#define cmdGetMode	'm'
// z - zero the frame buffer, abandon current cmd (1.15)
#define cmdZeroBuf	'z'
// v - return firmware version in four digits "0123" means version 1.23
#define cmdGetVer	'v'
// l - load cmd from specified buf: lP - PID, lD - DMR, lAnnxxxx - from PC where nn is slot num, xxxx - data
#define cmdLoadCmd	'l'
// q - set DIAGMDODE qualifier (3 bytes)
#define cmdSetQual	'q'
// d - snd cmdBuf content
#define cmdSendCmd	'd'
// aFFFTTT - dump memory from/to specified base addresses
#define cmdReadAdr	'a'
// s - set DCL speed (baudrate)
#define cmdSetSpeed	's'
#ifdef VER_RU
// u - update EEPROM (highly secret one!)
#define cmdSetEPR	'u'
#define suffixEPR	'E'
#endif
#ifdef VER_BY
// e - update EEPROM (highly secret one!)
#define cmdSetEPR	'e'
#define suffixEPR	'W'
#endif
// o - set options
#define cmdSetOpt	'o'
// p - payment complete, unlock adapter
#define cmdUnlock	'p'
#define cmdTestLock	'P'

// Echo Module ID command
volatile u08 cmdEchoID[11] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x82, 0x00, 0x00, 0x00, 0x83};
// Go CART mode command
volatile u08 cmdGoCART[11] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x04, 0x00, 0x00, 0x00, 0x05};

// Contains all 0..F frames w/o sync word. 30 bytes per frame.
// 1 byte - incremental counter of blocks 
// 2 byte - frame ID with vertical parity, status byte while engine running (v3!)
// 3 byte .. 30 byte - frame data (up to 0x0E words)
volatile u08 frBuf[0x10][30]; 
volatile u08 syncCART; 				// contain frame sync counter (got 1st frame ID)

volatile u08 cmdLength;				// length of current command in slots (words!), usually 1 slot, more for PID list transmission
volatile u16 addrFinish;			// end base address for memory dump

volatile u08 baudConst[2] = {0x00, 0xA0}; // TODO: make this work!
volatile u08 delay4Bit;
volatile u08 delay24Bit;
volatile u08 baudDefault;
volatile u08 cartHex;

volatile u08 workMode;
volatile u08 zeroCount;

// current byte to send pointer
volatile u08 *buf;
volatile u08 bufIndex, bufCount;

// CART Timer
volatile u08 frID;			// current frame ID w/o vertical parity
volatile signed char slotIdx;		// current slot number calculated with 24-bit timer
volatile signed char slotCount;		// number of slot expected in current block 
volatile signed char slotCountNext;	// number of slot expected in next block 
volatile u08 wordSync;		// byte of word being received index
volatile u08 wordData[5];	// bytes being received in current slot (v3!), wordSync as an index

volatile u08 cmdPending, cmdCurrent;	// should we issue a command in coming block...

// PC communication 
volatile u08 pcMode;			// sw uart working mode cmdXXXXXX0x0D: 
static volatile u08 pcBuff[40];		// buffer for receiving data from PC
static volatile u08 pcIndex;			// index for receiving buffer
static volatile u08 pcSend[40];		// buffer for sending data to PC
volatile u08 pcHead;			// index for adding to buffer
volatile u08 pcTail;			// index for reading from buffer
volatile u08 serialNumber[5];   // serial number is stored in eeprom at bytes 16..19
volatile u08 unlockNumber[20];  // unlock buffer, compare 1st 10 bytes with the following 10 bytes to match
volatile u08 demoMode;          // if not zero then demo mode

// ==========================================================
// This one is sync - return only when everything is sent
// Used only in initialization, so no need to do it async
// 
void SendBuffer(u08 *buffer, u08 len)
{
	sbi(PORTD, PDDL); // data direction line
	while (!(UCSR1A & (1<<UDRE1)) ); // 
	buf = buffer;
	bufIndex = 0;
	bufCount = len;
	if (len)               // if something to send
	{
		//cbi(UCSR1B, RXEN1);  // disable receive interrupt to ignore echo
		sbi(UCSR1B, UDRIE1); // enable UDR Empty interrupt 
	}
	else
	{
		cbi(PORTD, PDDL);   // reset data direction line
	}
	while ( (inb(PORTD) & (1<<PDDL)) ); // wait until all bytes sent
}

// ======================================================
// Baudrate const:
// 4th bit is stopbit flag
// low 4 bits are baudrate const index
//
#define br2400u	0x10		// 2 stop bits
#define br2400	0			// 1 stop bits
#define br4800	1			// 1 stop bit
#define br9600	2			// 1 stop bit
#define br19200	3			// 1 stop bit
//
void SetBaudrate(unsigned char brConst)
{
	unsigned char _sreg;

	_sreg = SREG; cli();
	switch(brConst)
	{
		case br19200:
			TCCR2B = 0b101;			// /128
			UBRR1L = LO(brd19200);
			UBRR1H = HI(brd19200);
			delay24Bit = 255 - (F_CPU/128*24/brc19200);
			delay4Bit = 255 - (F_CPU/128*4/brc19200) + 1;  // why +2 ?
			UCSR1C = 1<<UCSZ01|1<<UCSZ00|0<<USBS1; 
			break;
		case br9600:
			TCCR2B = 0b101;			// /128
			UBRR1L = LO(brd9600);
			UBRR1H = HI(brd9600);
			delay24Bit = 255 - (F_CPU/128/brc9600)*24;
			delay4Bit = 255 - (F_CPU/128/brc9600)*4 + 1;
			UCSR1C = 1<<UCSZ01|1<<UCSZ00|0<<USBS1; 
			break;
		case br4800:
			TCCR2B = 0b110;			// /256
			UBRR1L = LO(brd4800);
			UBRR1H = HI(brd4800);
			delay24Bit = 255 - F_CPU/brc4800*24/256;
			delay4Bit = 255 - F_CPU/brc4800/256*4 + 1;
			UCSR1C = 1<<UCSZ01|1<<UCSZ00|0<<USBS1; 
			break;
		case br2400:
			TCCR2B = 0b111;			// /1024
			UBRR1L = LO(brd2400);
			UBRR1H = HI(brd2400);
			delay24Bit = 255 - F_CPU/brc2400*24/1024;
			delay4Bit = 255 - F_CPU/brc2400*4/1024;
			UCSR1C = 1<<UCSZ01|1<<UCSZ00|0<<USBS1; 
			break;
		case br2400u:
			UBRR1L = LO(brd2400);
			UBRR1H = HI(brd2400);
// 			not used in UART mode
//			TCCR2B = 0b111;			// /1024
//			delay24Bit = 255 - (F_CPU/128/brc2400)*24;
//			delay4Bit = 255 - (F_CPU/128/brc2400)*4;
			UCSR1C = 1<<UCSZ01|1<<UCSZ00|1<<USBS1; 
			break;
	}
	SREG = _sreg;
}

// ======================================================
// Wait for freeing send buffer than send byte to PC 
//
void PCSendWait(u08 data)
{
	u08 _sreg;

	sbi(UCSR0B, UDRIE0);  				// explicitly enable UDRIE0
	while (pcTail != pcHead);
	_sreg = SREG; cli();
	pcSend[pcHead] = data;
	pcHead++;
	if (pcHead >= 40) pcHead = 0;
	SREG = _sreg;
}

// Send byte to PC
void PCSend(u08 data)
{
	u08 _sreg;

	_sreg = SREG; cli();
	pcSend[pcHead] = data;
	pcHead++;
	if (pcHead >= 40) pcHead = 0;
	SREG = _sreg;
}

// Send data inline - use only in interrupts!
static inline void PCSendInline(u08 data)
{
	pcSend[pcHead] = data;
	pcHead++;
	if (pcHead >= 40) pcHead = 0;
}

// convert 4-bit value into hex byte
inline u08 Nibble2Hex(u08 nibble)
{
	return ( (nibble <= 0x09)?(nibble + 0x30):(nibble - 9 + 0x40) );
}

// ======================================================
//
//
void InitStateFlags(void)
{
	//disable timer
	cbi(TIMSK2, TOIE2);
	sbi(TIFR2, TOV2);						// reset overflow flag
	// State Flags
	slotCount = 2;
	slotIdx = -1;
	wordSync = 1;
	wordData[1] = 0xFF;					// to catch the very first sync word
	//zeroCount = 0;
	//pcMode = 0;
	//pcIndex = 0;
	cmdCurrent = 0;
	workMode = modeNoMode;
}

// ======================================================
// CART Timer sequence
//
void cartTimerService(void)
{
	// F_CPU/128 - num of T2 ticks per second
	// brc9600 - num of bits per second
	TCNT2 =  delay24Bit; //255 - (F_CPU/128/brc9600)*24;
	slotIdx++;									
	wordSync = 1; 									// each timer tick is a new word!
	wordData[1] = 0xFF;
	if (slotIdx > slotCount) 
	{
		cbi(UCSR1B, UDRIE1); 						// disable UDR Empty interrupt 
		// don't disable (v3!) cbi(TIMSK2, TOIE2);							// disable TOI2 when got enough frames
		cbi(PORTD, PDDL);							// data direction line
		if (slotIdx > 30) InitStateFlags(); 	// switch to init seq when lost frame sync
	}
	else
	{
		// TODO: if no command to send
		if ((cmdCurrent & 0x60) == 0x40)
		{
			//cbi(UCSR1B, RXEN1);  					// disable receiver to ignore echo
			sbi(UCSR1B, UDRIE1); 					// enable UDR Empty interrupt 
//			sbi(PORTD, PDDL); 
		}
		else
		{
			cbi(PORTD, PDDL); 						// data direction line
		}
	}
}

// ======================================================
// Received byte interrupt handler
ISR(USART1_RX_vect)
{
	unsigned char RS, RSL;
	u16 addr;

	RS = UDR1;
	switch(workMode)
	{
		// ======== No Mode - wait for CART sequence for some time on base speed
		case modeNoMode:
			wordData[4] = wordData[3]; wordData[3] = wordData[2]; wordData[2] = wordData[1]; wordData[1] = RS;
			if ( (wordData[3] + wordData[4] == 0) && ( ((wordData[2]>>4) ^ (wordData[2] & 0xF) ^ (wordData[1] & 0xF) ^ 0xA) == (wordData[1]>>4) ))
				workMode = modeInCART;
			break;
		// ======== Wait for Echo ID responce on 2400 baud
		case modeWaitID:
			if (RS == 0x01) workMode = modeGoCART;
			break;
		// ======== Wait for CART mode sequence of 3 zeroes on 9600 baud than sync to 1st frame
		case modeInCART:
//				if ((zeroCount >= 3) && ( ((RS & 0x0F) ^ 0x0A) == (RS >> 4) ))  // Frame start!
				if ((wordData[1] == 0) && (RS == 0))		// sync word (v3!), next slot must be id word
				{
					// TODO: Reset status words in 5..16 frames to zero
					// reinit T2 with 4-bit delay
					cbi(TIMSK2, TOIE2);						// disable overflow int
					sbi(GTCCR, PSRASY);						// reset prescaler!
					TCNT2 = delay4Bit; //255 - (F_CPU/128/brc9600*4) + 2;	// delay between slots! ^^|_|^|_|^|_|^^
					sbi(TIFR2, TOV2);						// reset overflow flag
					sbi(TIMSK2, TOIE2);						// enable overflow int
					slotIdx = -1;
				}

				if ( (slotIdx == 0) && (wordSync > 1) && ( ((wordData[1] & 0x0F) ^ (wordData[1]>>4) ^ (RS & 0x0F) ^ 0x0A) == (RS >> 4) ) )		// now that's a frame start!, RS contain FrameID
				{
					frID = RS & 0x0F;

//					if (frID < 4) 							// got command frame (one of 1st four)
//					{
						if (frID == 0)						// got 1st frame!
						{
							sbi(PORTD, PDDL);					// data direction line
							syncCART++; 
							sbi(PINC, PLED);				// toggle blinker LED
							slotCount = slotCountNext;		// slot count 2 by default on current block/frame
							slotCountNext = 2;				// default slot count for next block (ovride when feed some cmd)

							if (cmdCurrent)					// this will be true in 2nd block with cmd feed!
							{
								cmdLength = 0;
								if (cmdCurrent > 0x60)		// small letter cmd, TODO: and some "got result" flag
								{
									switch (cmdCurrent)
									{
										//case 'f':
										//	cmdCurrent = 'f';
										//	break;
										case 'm':
											//SetBaudrate(br2400); // TODO: baudrate set after last frame!
											cmdCurrent = 0;
											break;
										default:
											cmdCurrent = 0;
											break;
									}
								}
								else
								{
									cmdCurrent = cmdCurrent + 0x20; 			// "waiting for response" mode 
									switch (cmdCurrent)
									{
										case 'd':
											if (!(frBuf[7][2] & 0x40))				// if self test incomplete
											{
												cmdLength = 1;
												cmdCurrent = 'D';					// still send D...
											}
											break;
										case 'e':
//											if (frBuf[4][2] == cmdData[4][0])
//											{
//												cmdLength = (cmdBuf[2][1] & 0x0F);
//												cmdCurrent = 'R';					// switch to Q after 2nd block of E
//											}
//											else
											{
												cmdLength = (cmdBuf[2][1] & 0x0F);
												cmdCurrent = 'R';					// 
											}
											break;
										case 'i':
											if (frBuf[4][2] == cmdData[8][0])
											{
												cmdCurrent = 'Q';					// immediately switch to Q after I
											}
											else
											{
												cmdCurrent = 'I';					// keep I mode until current cmd is 0x41!
											}
											cmdLength = (cmdBuf[2][1] & 0x0F);
											break;
										case 'q':
//											if (frBuf[4][2] == cmdData[16][0])
											{
												cmdCurrent = 'R';					// keep mode until current cmd is 0x21
											}
											//cmdLength = 0;
											cmdLength = (cmdBuf[2][1] & 0x0F);	// while small q mode - EEC saves PID list in its RAM
											break;
										case 'g':
											cmdLength = 1;
											cmdCurrent = 'G';
											break;
										case 'k':
											addr = ((cmdBuf[3][0] | (cmdBuf[3][1]<<8)) + 4) & 0xFFF;  // curr addr, +4(*16) in offs map
											//addr = (addr + 4);  // why +4??
											if (addr >= addrFinish)
											{
												//
											}
											else
											{
												cmdLength = 1;
												cmdCurrent = 'K';
												cmdBuf[3][0] = addr & 0xFF;
												cmdBuf[3][1] = ((addr>>8) & 0xF) | (VPARITY(cmdBuf[3][0], ((addr>>8) & 0xF)));
											}
											break;
										case 'a':
											cmdLength = 1;
											cmdCurrent = 'R';
											break;
										case 'm':
											cmdLength = 2;
											break;
										default:
											cmdLength = 0;
											break;
									}
								}
							} // cmdCurrent

							if ((cmdPending) && (!cmdCurrent)) // we have some cmd to issue and no previous cmd
							{
								cmdCurrent = cmdPending;	// 
								cmdLength = 1;				// TODO: update with actual value based on cmd type!
								cmdPending = 0;				// 
							}
							if ((cmdCurrent & 0x60) == 0x40)			// CAPITAL letter cmd - update cmd buffer
							{
								cmdBuf[2][0] = cmdData[cmdCurrent - 0x41][0];
								cmdBuf[2][1] = cmdData[cmdCurrent - 0x41][1];
								slotCountNext = (cmdBuf[2][1] & 0x0F);	// slot count for next block from cmd diagmode
							}
						}  // frID == 0
//					}   // frID < 4

					if (cmdCurrent) frBuf[frID][0] = syncCART; 	// 1st byte - index of current block
					frBuf[frID][1] = wordData[1]; 				// 2nd byte - engine status byte
					if (cmdCurrent){
						PCSendInline(0xFF);
						if (!cartHex)
						{
							PCSendInline((frID << 4));
							PCSendInline(syncCART);
							PCSendInline(wordData[1]);
						}
						else
						{
							PCSendInline(Nibble2Hex( (((frID << 4) )>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( ((frID << 4) ) & 0x0F ));
							PCSendInline(Nibble2Hex( (syncCART>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( syncCART & 0x0F ));
							PCSendInline(Nibble2Hex( (wordData[1]>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( wordData[1] & 0x0F ));
						}
					}
				}	////////////////////////// frame start
			// send data stream to PC
			if ((wordSync < 3))
			{
				wordData[wordSync] = RS;
				if ((slotIdx >= 1) && (slotIdx <= slotCount))
				{
					frBuf[frID][slotIdx*2 + wordSync - 1] = RS;
					RSL = frBuf[frID][slotIdx*2 + wordSync - 2];
					// first send offset in row-col nibbles
					if ((wordSync == 2) && ( ((RSL>>4) ^ (RSL & 0xF) ^ (RS & 0xF) ^ 0xA) == (RS>>4) )) 
					{
						PCSendInline(0xFF);
						if (!cartHex)
						{
							PCSendInline((frID << 4) + slotIdx);
							PCSendInline(RSL);
							PCSendInline(RS);
						}
						else
						{
							PCSendInline(Nibble2Hex( (((frID << 4) + slotIdx)>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( ((frID << 4) + slotIdx) & 0x0F ));
							PCSendInline(Nibble2Hex( (RSL>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( RSL & 0x0F ));
							PCSendInline(Nibble2Hex( (RS>>4) & 0x0F ));
							PCSendInline(Nibble2Hex( RS & 0x0F ));
						}
					}
					//PCSendInline(Nibble2Hex( (RS>>4) & 0x0F ));
					//PCSendInline(Nibble2Hex( RS & 0x0F ));
				}
				wordSync++;
			}
			else
			{
				// we are here only when we lose sync slots AND T2 timer is stopped
				if (RS) wordSync = 1; else wordSync = 2;
			}
			break;
	}
}

// ====== Transmit Complete when no data in UDR since last UDRIE =======================
//
ISR(USART1_TX_vect)
{
	if (!(UCSR1B & (1<<UDRIE1))) 
	{
//		delay_us(10);
		cbi(PORTD, PDDL);
	}
	//sbi(UCSR1B, RXEN1); 	// enable receiver
}

// ===============================================
// UDR ready to receive next byte interrupt
// This one fires just after being enabled!
//
ISR(USART1_UDRE_vect)
{
	// TODO: Send long CMD in CART - only two bytes from current slotIdx of CMD buf, 
	switch (workMode)
	{
		case modeInCART:
			if (cmdCurrent) 
			{
				if (slotIdx <= cmdLength) 
				{
					if ( (wordSync < 3) && ( ((frID < 4) && (slotIdx == 1)) || ((slotIdx > 1) & (frID < 16) ) ) )
					{
						sbi(PORTD, PDDL); 							// data direction line
						if ( (cmdBuf[frID][(slotIdx-1)*2]) || (cmdBuf[frID][(slotIdx-1)*2+1]) )  // if not zero
						{
							UDR1 = cmdBuf[frID][(slotIdx-1)*2+wordSync-1];	// send it
						}
						wordSync++;									// next byte
					}
				}
				else
				{
					cbi(PORTD, PDDL); 								// data direction line
					cbi(UCSR1B, UDRIE1);							// disable UDR Empty Interrupt
					//sbi(UCSR1B, RXEN1);								// enable receiver
				}
			}
			break;
		default:
			if (bufIndex < bufCount)
			{
				UDR1 = *buf++;
				bufIndex++;
			}
			else
			{
				cbi(UCSR1B, UDRIE1);  // disable UDR Empty Interrupt
				bufIndex = 0;
			}
			break;
	}  // switch
}

// ======================================================
// UDR empty interrupt handler
ISR(USART0_UDRE_vect)
{
	if (pcTail != pcHead)
	{
		UDR0 = pcSend[pcTail];
		pcTail++;
		if (pcTail >= 40) pcTail = 0;
	}
	else
		cbi(UCSR0B, UDRIE0);  // disable UDR Empty Interrupt
}

// ======================================================
// Transmit complete interrupt handler
ISR(USART0_TX_vect)
{
	cbi(UCSR0B, UDRIE0);  // disable UDR Empty Interrupt
}

// ======================================================
// Received byte from PC interrupt handler
ISR(USART0_RX_vect)
{
	unsigned char RS;

	RS = UDR0;
	if (RS != 0x0D)  // not enter - fill buffer
	{
		pcBuff[pcIndex] = RS;
		pcIndex++;
		if (pcIndex >= 40)  // don't allow buffer overflow
		{
			pcIndex = 0;
			pcMode = 0;
		}
	}
	else
		pcMode = pcBuff[0]; 		// assume 1st byte is mode ID, enter repeats prev cmd!
}


int main (void) {

	u08 i, j;
	u16 addr;

	// disable watchdog
	wdt_disable();

	InitStateFlags();

	// some options
	baudDefault = eeprom_read_byte( (uint8_t*)optDefaultBaudrate );
	if (baudDefault == 0xFF) baudDefault = '2';
	cartHex = (eeprom_read_byte( (uint8_t*)optCartHex ) == '1');

	// demo mode or not
	eeprom_read_block((void*)&unlockNumber, (const void*)42, 10);
	demoMode = 0;
	for (i=0;i<10;i++){
		demoMode = demoMode | (unlockNumber[i] ^ 0xFF);// ^ unlockNumber[i + 10]);
	}
	//demoMode = 0;

	// Init USART1 - EEC-IV communication
	SetBaudrate(baudDefault - 0x30);
	UCSR1A = 0;
	UCSR1B = 1<<RXEN1|1<<TXEN1|1<<RXCIE1|1<<TXCIE1;

	// Init USART0 - PC comm. 38400/8N1
	UBRR0L = LO(brd38400);
	UBRR0H = HI(brd38400);
	UCSR0A = 0;
	UCSR0B = 1<<RXEN0|1<<TXEN0|1<<RXCIE0|1<<TXCIE0;
	UCSR0C = 1<<UCSZ01|1<<UCSZ00|0<<USBS1; 

	// Init PORTs, TODO: pull-up for all unused ports!
	DDRA = 0xFF;		// TODO: debugging purposes!
	//PORTA = 0xFF;

	// Power reduce
	PRR = 0b10000100;

	// Misc init
	sbi(DDRC, PLED); 	// enable debug LED pin output
	DDRD = (1<<PDDL);
	//sbi(DDRD, PDDL); 	// enable data direction line output pin for 485 driver
	timerInit();    	// we use T0, T1, T2
	cbi(TIMSK2, TOIE2);	// disable overflow
	TCCR2A = 0;			// basic T2 mode, TCCR2B init with prescaler
	timerAttach(TIMER2OVERFLOW_INT, cartTimerService);

	if (demoMode) {InitDemoPIDMap();} else {InitDefaultPIDMap();}

	sei();

	// ============== Main cycle
	while(1)
	{
		// ============== PC commands handling
		if (pcMode)
		{
			switch (pcMode)
			{
				case cmdReboot:
					PCSend('$');
					sbi(UCSR0B, UDRIE0);  				// explicitly enable UDRIE0 before reset
					wdt_enable(1); cli(); while(1);
					break;
				case cmdSwCART:
					cmdCurrent = 0;
					workMode = modeNoMode;
					PCSend(workMode);
					break;
				case cmdGetMode:
					PCSend(workMode);
					//PCSend(slotCount + 0x30);
					PCSend(cmdPending);
					PCSend(cmdCurrent);
					break;
				case cmdSetCode:
					cmdPending = pcBuff[1];
					PCSend(cmdPending);
					break;
				case cmdLoadCmd:			
					switch (pcBuff[1])
					{
						case 'P':
							if (demoMode) {InitDemoPIDMap();} else {InitDefaultPIDMap();}
							break;
						case 'D':
							if (!demoMode) InitDefaultDMRMap();
							break;
						case 'T':
							if (!demoMode) InitTestPIDMap();
							break;
						case 'B':
							InitDefaultBaudMap();
							break;
						case 'A':
							i = NIB2BYTE(pcBuff[3]);
							j = NIB2BYTE(pcBuff[2]);
							if (!demoMode){
								cmdBuf[j][i*2] = NIB2BYTE(pcBuff[7]) | (NIB2BYTE(pcBuff[6])<<4);
								cmdBuf[j][i*2+1] = VPARITY(cmdBuf[j][i*2], NIB2BYTE(pcBuff[5]));
							}
							//cmdBuf[j][i*2+1] = NIB2BYTE(pcBuff[5]) | (NIB2BYTE(pcBuff[4])<<4);
							break;
					}
					PCSendWait(pcBuff[1]);
					break;
				case cmdSetQual:
					SetQualifier(pcBuff[1], pcBuff[2], pcBuff[3]);
					PCSend(Nibble2Hex( (cmdBuf[3][1]>>4) & 0x0F ));
					PCSendWait(Nibble2Hex( cmdBuf[3][1] & 0x0F));
					break;
				case cmdReadAdr:
					// finish address shifted 4 bits
					addrFinish = ((NIB2BYTE(pcBuff[4])<<8) | (NIB2BYTE(pcBuff[5])<<4) | NIB2BYTE(pcBuff[6])) - 1;  // 0x10 offs map
					// start address - directly to current qualifier
					SetQualifier(pcBuff[1], pcBuff[2], pcBuff[3]);
					PCSend('A');
					//PCSend(Nibble2Hex( (addrFinish>>8) & 0x0F ));
					//PCSend(Nibble2Hex( (addrFinish>>4) & 0x0F ));
					//PCSendWait(Nibble2Hex( addrFinish & 0x0F));
					cmdPending = 'K';
					break;
				case cmdSendBuf:
					PCSend(0x0D);
					for (i=0;i<16;i++)
					{
						for (j=0;j<30;j++)
						{
							PCSend(Nibble2Hex( (frBuf[i][j]>>4) & 0x0F ));
							PCSendWait(Nibble2Hex( frBuf[i][j] & 0x0F));
						}
						PCSendWait(0x0D);
					}
					break;
				case cmdSendCmd:
					PCSend(0x0D);
					for (i=0;i<16;i++)
					{
						for (j=0;j<28;j++)
						{
							PCSend(Nibble2Hex( (cmdBuf[i][j]>>4) & 0x0F ));
							PCSendWait(Nibble2Hex( cmdBuf[i][j] & 0x0F));
						}
						PCSendWait(0x0D);
					}
					break;
				case cmdZeroBuf:
					cmdCurrent = 0;
					for (i=0;i<16;i++)
						for (j=0;j<30;j++)
							frBuf[i][j] = 0;
					PCSendWait('!');
					break;
				case cmdGetVer:					// version is 1.xx
					if (demoMode) {PCSend('D');} else {PCSend('0');}
					PCSend('1');
					PCSend('2');
					PCSendWait('7');
					// send serial number too
					eeprom_read_block((void*)&serialNumber, (const void*)16, 5);
					for (i=0;i<6;i++)
						PCSend(serialNumber[i]);
					break;
				case cmdSetSpeed:
				    if ((pcBuff[1] >= '0') && (pcBuff[1] <= '9'))
					{
						SetBaudrate(pcBuff[1] - 0x30);
						PCSend(pcBuff[1]);
					}
					else
					{
						PCSend(baudDefault);
					}
					break;
				// uENNNNxxxxxxxx (RU), eWNNNNxxxxxx (BY) - where NNNN addr in hex, xxxxx - values as is (must be chars)
				case cmdSetEPR:
					if ((!demoMode) && (pcBuff[1] == suffixEPR))
					{
						addr = (NIB2BYTE(pcBuff[2])<<12) | (NIB2BYTE(pcBuff[3]) << 8) | (NIB2BYTE(pcBuff[4])<<4) | NIB2BYTE(pcBuff[5]);
						PCSend(pcBuff[2]);
						PCSend(pcBuff[3]);
						PCSend(pcBuff[4]);
						PCSend(pcBuff[5]);
						i = 6;
						while (i < pcIndex) {
							eeprom_busy_wait();
							eeprom_write_byte((uint8_t*)(addr + i - 6), pcBuff[i]);
							PCSend(pcBuff[i]);
							i++;
						}
					}
					else
					{
						PCSend('?');
						PCSend(cmdSetEPR);
					}
					break;
				// p912B053530 - unlock with a 10 char code
				case cmdUnlock:
				case cmdTestLock:
					// if no demo - no need to unlock
					if (!demoMode) {
						PCSend('?');
						PCSend(cmdUnlock);
						break;
					}
					// if supplied code matches the stored code
					for (i=1;i<=10;i++){
						demoMode = 0;
						demoMode = demoMode | (unlockNumber[i-1] ^ pcBuff[i]);
					}
					if (!demoMode) PCSend('!');
					// then clear the stored code with 0xFF 
					if (!demoMode && (pcMode == cmdUnlock)){
						for (i=1;i<=10;i++){
							eeprom_busy_wait();
							eeprom_write_byte((uint8_t*)(i + 41), 0xFF);
						}
					}
					// reboot!
					PCSend('$');
					sbi(UCSR0B, UDRIE0);  				// explicitly enable UDRIE0 before reset
					wdt_enable(1); cli(); while(1);
					break;
				case cmdSetOpt:
					// set some option (or read all if no params)
					if ((pcBuff[1] >= '0') && (pcBuff[1] <= '9'))
					{
						eeprom_busy_wait();
						eeprom_write_byte((uint8_t*)(pcBuff[1] - 0x30), pcBuff[2]);
						PCSend(cmdSetOpt);
						PCSend(pcBuff[1]);
					}
					else
						for (addr=0;addr<10;addr++)
							PCSend(eeprom_read_byte( (uint8_t*)addr ));
					break;
				default:
					PCSend('?');
					for (i=0; i < pcIndex; i++)
					{
						PCSend(pcBuff[i]);
					}
					break;
			}
			pcMode = 0;
			pcIndex = 0;
		}  // pcMode
		// ============== EEC-IV comm mode handling
		switch(workMode)		
		{
			// ============= Wait for CART
			case modeNoMode:
				delay_ms(100);			// We'll catch 3 zeroes within this time period
				if (workMode != modeInCART) workMode = modeEchoID;
				break;
			// ============= Hello 
			case modeEchoID:
				sbi(PORTC, PLED);
				//delay_ms(100);
				//PCSend(workMode);
				SetBaudrate(br2400u);
				// Transmit echo module id
				SendBuffer((void *)cmdEchoID, 11);
				workMode = modeWaitID;
				break;
			// ============= Wait for hello responce
			case modeWaitID:
				cbi(PORTC, PLED);

				delay_ms(1000);
				if (workMode == modeWaitID) 
					workMode = modeEchoID;  // return to Echo Module ID if still no answer
				break;
			// ============= Go CART
			case modeGoCART:
				zeroCount = 0;
				// Transmit Go CART
				SendBuffer((void *)cmdGoCART, 11);
				SetBaudrate(baudDefault - 0x30); // 
				workMode = modeInCART;
				break;
			// ============= CART Mode Active!
			case modeInCART:
				//if (cmdCurrent) PCSend(cmdCurrent);
				break;
		}
		if (pcHead != pcTail)
		{
			sbi(UCSR0B, UDRIE0);  // enable UDR Empty Interrupt
		}
	}
}
