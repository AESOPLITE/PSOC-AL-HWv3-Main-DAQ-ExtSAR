/* ========================================
 *
 * Brian Lucas
 * Copyright Bartol Research Institute, 2020
 * All Rights Reserved
 * UNPUBLISHED, LICENSED SOFTWARE.
 *
 * CONFIDENTIAL AND PROPRIETARY INFORMATION
 * WHICH IS THE PROPERTY OF Bartol Research Institute.
 *
 *
 * Firmware for the Main PSOC on the AESOPLite DAQ board
 * V0.0 DON'T Run on new 2021 Backplane, developed on Lee backplane. basic commands forward to backplane event psoc.  Data is running with filler and not aware of Event PSOC data structure.
 * V1.0 Changes to Select lines for new 2021 backplane
 * V1.1 Added I2C handling since bus is now divided
 * V1.2 Changed Init commands for T2 testing with python script
 * V1.3 Added RTC internal initilization from I2C RTC
 * V1.4 Added RTC write default date to I2C RTC
 * V1.6 Build large buffer for output frames
 * V1.7 Frame buffer now outputs event and SPI without filler frames 
 * V1.8 Adding initial houskeeping output 
 * V1.9 Adding initial baro output 
 * V1.10 Adding all baros temp and press
 * V2.0 DON'T RUN on V2 Hardware this is a transition version to V3 with Ext SAR ADC
 * V2.1 Corrected pinout to reenable nDataReady, spi, and add Event Reset for use with V5 and higher Event PSOC
 * V2.2 Fix frame numbering, init commands for tracker testing
 * V2.3 Fix stale frame data issue introduced in last fix
 * V2.4 Remove USB data placeholder for Low Rate packet data that was overflowing to other mem 
 * V2.5 Fix UART HR output skipping frames 
 * V2.6 Change UART HR to use DMA instead of software buffer 
 * V2.7 Init tracker to use new tracker trigger cable 
 * V2.8 Init commands for new v23 Event PSOC with housekeeping
 * V3.0 Add RTC sequence at startup to read i2c and set Main + Event
 * V3.1 Changed how init commands are copied after RTC. Tuned the RTC seq start delay
 * V3.2 Changed init commands and reordered for flight prep
 * V3.3 Housekeeping format change to new format from mock Counter1. Disabled command isr till init   
 * V3.4 Added Low Rate Science Data Packet just Main HK for ths version
 * V3.5 Added more of the Main HK values
 * V3.6 Added more handling of the I2C baro
 * V3.7 Fixed I2C Barometer_COE_PTAT21 register location, changed ForcedSampleBaroI2CBytes, use i2c no stop mode with baro
 * V3.8 Roll back ForcedSampleBaroI2CBytes & no stop changes
 * V3.9 Moved Barometer 1 & 2 Pressure, Temp & Time capture to ISR 
 * V3.10 Changed interupt priorities to elevate Event SPI reading
 * V3.11 Adding low rate copy of Event HK
 * V3.12 Adding handling for end of low rate copy of Event HK
 * V3.13 Added delay before RTC, fixed some RTC I2C bit ops
 * V3.14 Increased delay before RTC to 1 sec to give event PSOC startup time
 * V3.15 Fixed length of low rate, copy of mainHK & changed some init commands
 * V3.16 Added missing values to Main HK execpt for Die Temp
 * V3.17 Fixed bitmasking of Main HK
 * V3.18 Fixed frame dropped packet copy, added DieTemp Measurement
 * V3.19 Removed obsolete init timing calibration, changed init T2 threshold 
 * V3.20 Added Busy Event PSOC Signal Pin
 * V3.21 Frame Buffer increased to availiable SRAM, removed init commands obsolete by new Event PSOC firmware
 * V3.22 Change init commands for layer 6 tracker swap
 * V3.23 Change init commands for T2 & T3
 * V3.24 Copy 3 more event HK bytes
 * V4.0 Added main command interpretation, starting with RTC
 *
 * ========================================
*/


#include "project.h"
#include "stdio.h"
#include "string.h"
#include "math.h"
#include "errno.h"

#define MAJOR_VERSION 4 //MSB of version, changes on major revisions, able to readout in 1 byte expand to 2 bytes if need
#define MINOR_VERSION 0 //LSB of version, changes every settled change, able to readout in 1 byte
#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
//#define WRAPINC(a,b) (((a)>=(b-1))?(0):(a + 1))
#define WRAPINC(a,b) ((a + 1) % (b))
#define WRAP3INC(a,b) ((a + 3) % (b))
#define WRAPDEC(a,b) ((a + ((b) - 1)) % (b))
#define WRAP(a,b) ((a) % (b)) //Macro to bring new calculated index a into the bounds of a circular buffer of size b
#define ISELEMENTDONE(a,b,c) ((b <= c) ? ((a < b) || (a >= c)) : ((a < b) && (a >= c)) )//used to determine if element in circular buffer is done 
#define ACTIVELEN(a,b,c) ((((c) - (a)) + (b)) % (c)) //Macro to calculate active length between a and b in circular buffer of size c. Exclusive, need to add 1 to make inclusive
// From LROA103.ASM
//;The format for the serial command is:
//; S1234<sp>xyWS1234<sp>xyWS1234<sp>xyW<cr><lf>
//; where 1234 is an ASCII encoded 16 bit command, with the format:
//; Data Byte for boards:	1 = MSB high nibble, 2 = MSB low nibble
//; Address Byte for boards: 3 = LSB high nibble, 4 = LSB low nibble
//; S & W are literal format characters,<sp> = space, xy = CIP address (ignored).
//; 9 characters are repeated 3 times followed by a carriage return - line feed,
//; and all alpha characters must be capitalized, baud rate = 1200.
#define START_COMMAND	(uint8*)("S") //Start command string before the 4 command char 
#define START_COMMAND_SIZE	1u //Size of Start command string before the 4 command char 
#define END_COMMAND	(uint8*)(" 01W") //End command string after the 4 command char, CIP is 01 which is ignored
#define END_COMMAND_SIZE	 4u //Size of End command string after the 4 command char, CIP is 01 which is ignored
#define CR	(0x0Du) //Carriage return in hex
#define LF	(0x0Au) //Line feed in hex
#define DLE	(0x10u) //Data Link Escape Used as low rate packet header
#define ETX	(0x03u) //Data Link Escape Used as low rate packet trailer
#define CMD_ID	(0x14u) //ID byte for command in low rate packet
#define REQ_ID	(0x13u) //ID byte for request science data in low rate packet
#define SDATA_ID	(0x53u) //ID byte for science data in low rate packet
#define FILLBYTE (0xA3u) //SPI never transmits  so could be anything
//#define CMDBUFFSIZE 3
/* Project Defines */
#define FALSE  0
#define TRUE   1
#define SPI_BUFFER_SIZE  (512u)
//#define SPI_BUFFER_SIZE  (1024u)
#define EV_BUFFER_SIZE  (1024u)
typedef uint16 SPIBufferIndex; //type of variable indexing the SPI buffer. should be uint8 or uint16 based on size
typedef uint16 EvBufferIndex; //type of variable indexing the Event buffer. should be uint16
//uint8 cmdBuff[CMDBUFFSIZE];
//uint8 iCmdBuff = CMDBUFFSIZE - 1;

#define USBFS_DEVICE	(0u)
/* The buffer size is equal to the maximum packet size of the IN and OUT bulk
* endpoints.
*/
#define USBUART_BUFFER_SIZE	(64u)
#define LINE_STR_LENGTH	(20u)

//#define SELLOW_PERIOD	(16u)

//#define NUM_SPI_DEV	(5u)
#define NUM_SPI_DEV	(1u)
uint8 iSPIDev = 0u;
//uint8 frameSPIDev = 0u;
//#define POW_SEL		(0x01u)
//#define PHA_SEL		(0x02u)
//#define CTR1_SEL	(0x03u)
//#define TKR_SEL		(0x0Bu)
//#define CTR3_SEL	(0x0Cu)
//const uint8 tabSPISel[NUM_SPI_DEV] = {POW_SEL, PHA_SEL, CTR1_SEL, TKR_SEL, CTR3_SEL};
//const uint8 tabSPISel[NUM_SPI_DEV] = {0, 0, CTR1_SEL, 0, CTR3_SEL};
//const uint8 tabSPISel[NUM_SPI_DEV] = {0, 0, 0, 0, 0}; //DEBUG
const void (* tabSPISel[NUM_SPI_DEV])(uint8) = {
    Pin_Sel2_Pwr_Write}; //function pointers to write to the pins for diffent select lines
#define NULL_HEAD	(0xF9u)
#define POW_HEAD	(0xF6u)
#define PHA_HEAD	(0xF3u)
#define CTR1_HEAD	(0xF8u)
#define TKR_HEAD	(0xF4u)
#define CTR3_HEAD	(0xFAu)
#define EOR_HEAD	(0xFFu)
#define DUMP_HEAD	(0xF5u)
#define ENDDUMP_HEAD	(0xF7u)
#define EVFIX_HEAD	(0xDBu) //Event PSOC fixed length packet
#define EVVAR_HEAD	(0xDCu) //Event PSOC variable length packet
#define EVHK_ID	(0xDEu) //Event PSOC HK ID
const uint8 tabSPIHead[NUM_SPI_DEV] = {POW_HEAD}; //only power boards left , PHA_HEAD, CTR1_HEAD, TKR_HEAD, CTR3_HEAD};
const uint8 frame00FF[2] = {0x00u, 0xFFu};
uint8 buffSPI[NUM_SPI_DEV][SPI_BUFFER_SIZE];
SPIBufferIndex buffSPIRead[NUM_SPI_DEV];
SPIBufferIndex buffSPIWrite[NUM_SPI_DEV];
SPIBufferIndex buffSPICurHead[NUM_SPI_DEV]; //Header of the current packet
SPIBufferIndex buffSPICompleteHead[NUM_SPI_DEV]; //Header of the latest complete packet
uint8 buffEv[EV_BUFFER_SIZE];
EvBufferIndex buffEvRead;
EvBufferIndex buffEvWrite;
EvBufferIndex buffEvWriteLast = 0u;

enum readStatus {CHECKDATA, READOUTDATA, EORFOUND, EORERROR};
enum commandStatus {WAIT_DLE, CHECK_ID, CHECK_LEN, READ_CMD, CHECK_ETX_CMD, CHECK_ETX_REQ};
enum eventLowRateCopyState {NO_EVENT_LR_COPY, COPY_EVENT_HK, COPY_LAST_EVENT};//
#define COMMAND_SOURCES 3
enum commandStatus commandStatusC[COMMAND_SOURCES];
enum eventLowRateCopyState eventLRCopy = COPY_EVENT_HK;//default to HK copy
uint8 commandLenC[COMMAND_SOURCES];//current command length expected from each source
uint8 cmdRxC[COMMAND_SOURCES][2];//current commands bytes being received from each source
#define COMMAND_CHARS	(4u)
uint8 curCmd[COMMAND_CHARS+1]; //one extra char for null
//uint8 iCurCmd = 0u;
//volatile uint8 timeoutDrdy = FALSE;
//volatile uint8 lastDrdyCap = 0u;
//#define MIN_DRDY_CYCLES 4 //8 //might need  Fster clock since the master clock generates noise the noise on this line
 
const uint8 frameSync[2] = {0x55u, 0xABu};
uint32 frameCnt = 0u; //TODO Comment this out when ISR is removed
//#define DATA_BYTES_FRAME 27

typedef struct PacketEvent {
	EvBufferIndex header;
	EvBufferIndex EOR; //last byte (inclusive) in the read should be LSB FF of FF00FF  
} PacketEvent;

#define PACKET_EVENT_SIZE	 (16u)
PacketEvent packetEv[PACKET_EVENT_SIZE];
uint8 packetEvHead = 0u;
uint8 packetEvTail = 0u;

typedef struct PacketLocation {
	SPIBufferIndex index;
	SPIBufferIndex header;
	SPIBufferIndex EOR; //last byte (inclusive) in the read should be LSB FF of FF00FF  
} PacketLocation;

#define PACKET_FIFO_SIZE	 (16u * NUM_SPI_DEV)
PacketLocation packetFIFO[PACKET_FIFO_SIZE];
uint8 packetFIFOHead = 0u;
uint8 packetFIFOTail = 0u;

uint8 buffUsbTx[USBUART_BUFFER_SIZE];
uint8 iBuffUsbTx = 0;
uint8 buffUsbTxDebug[USBUART_BUFFER_SIZE];
uint8 iBuffUsbTxDebug = 0;

#define FRAME_DATA_BYTES	(27u)
#define FRAME_BUFFER_BLOCKS	(6u) //Number of blocks in the buffer, should me changed based on availiaable SRAM. 256 frames takes about 14%
#define FRAME_BUFFER_BLOCK_SIZE	(256u) //choosen so LSB of seq can be preset in buffer
#define FRAME_BUFFER_SIZE	(FRAME_BUFFER_BLOCKS * FRAME_BUFFER_BLOCK_SIZE) //Calculate size, do not change 
typedef struct FrameOutput {
	uint8 seqH;
	uint8 seqM;
	uint8 seqL;
	uint8 sync[4];
	uint8 data[FRAME_DATA_BYTES];
} FrameOutput;
typedef uint16 FmBufferIndex; //type of variable indexing the Frame buffer. should be uint16

FrameOutput buffFrameData[FRAME_BUFFER_SIZE];
//uint8 buffFrameData[FRAME_BUFFER_SIZE][FRAME_DATA_BYTES];
FmBufferIndex buffFrameDataRead = 0;
FmBufferIndex buffFrameDataReadUSB = 0;
FmBufferIndex buffFrameDataWrite = 0;

uint16 seqFrame2HB = 0; //2 Highest bytes of the frame seq (seqH & seqM) the seqL is set by init

uint16 cntFramesDropped = 0; // number of frames overwritten before being sent via RS232
uint16 cntFramesDroppedUSB = 0; // number of frames overwritten before being sent via USB

#define HK_BUFFER_PACKETS	(2u) //Number of houskeeping packets to buffer, min 2 
#define HK_PAD_SIZE	21 //number of padding bytes need for 
//typedef struct HousekeepingPeriodic { //intended to Mimic Counter 1 (Power-Counter  Formats V3.txt) for early baro testing 
//	uint8 header[3];
//	uint8 version[2];
//	uint8 secs[4];
//	uint8 paddingTemp[21];
//	uint8 baroTemp1[3];
//	uint8 baroPres1[3];
//    uint8 baroTemp2[3];
//	uint8 baroPres2[3];
//	uint8 padding[HK_PAD_SIZE];
//	uint8 EOR[3];
//} HousekeepingPeriodic;
//typedef struct HousekeepingPeriodic {// swaped pres and temperature for debug
//	uint8 header[3];
//	uint8 version[2];
//	uint8 secs[4];
//	uint8 paddingTemp[21];
//	uint8 baroPres1[3];
//	uint8 baroTemp1[3];
//	uint8 baroPres2[3];
//    uint8 baroTemp2[3];
//	uint8 padding[HK_PAD_SIZE];
//	uint8 EOR[3];
//} HousekeepingPeriodic;
typedef struct HousekeepingPeriodic {
	uint8 header[3];
    uint8 packedTimeDate[4];//
    uint8 commandLast[2];//
    uint8 commandCount[2];//
    uint8 commandErrors;//
    uint8 generalErrors;//
    uint8 missingValuesThisPacket;//
    uint8 fifoPercentFull;//0-100
    uint8 framesDroppedRS232[2];//
    uint8 framesDroppedUSB[2];//
	uint8 baroPres1[4];
	uint8 baroTemp1[4];
	uint8 baroPres2[4];
    uint8 baroTemp2[4];
    uint8 baroPres3[3];//I2C Address 1110000
    uint8 baroTemp3[3];//I2C Address 1110000
    uint8 boardTemperature[2];//I2C Address 1001000
    uint8 coreDieTemp[2];//
    uint8 digital3VVoltage[2];//I2C Address 1000100
    uint8 digital3VAmperage[2];//I2C Address 1000100
    uint8 analog3VVoltage[2];//I2C Address 1000011
    uint8 analog3VAmperage[2];//I2C Address 1000011
    uint8 digital5VVoltage[2];//I2C Address 1000001
    uint8 digital5VAmperage[2];//I2C Address 1000001
    uint8 analog5VVoltage[2];//I2C Address 1000101
    uint8 analog5VAmperage[2];//I2C Address 1000101
    uint8 digital15VVoltage[2];//I2C Address 1000010
    uint8 trackerVoltage[2];//I2C Address 1000000
    uint8 trackerAmperage[2];//I2C Address 1000000
    uint8 trackerBiasVoltage[2];//I2C Address 1000110
	uint8 EOR[3];
} HousekeepingPeriodic;

HousekeepingPeriodic buffHK[HK_BUFFER_PACKETS];
uint8 buffHKRead = 0;
uint8 buffHKWrite = 0;

#define HK_HEAD	(0xD0u) //ID for Main PSOC Housekeeping
//#define HK_HEAD	(0xF8u) //usign counter1 for main PSOC hk right now DEBUG

//#define COUNTER_PACKET_BYTES	(45u)

typedef struct LowRateHousekeeping {
	uint8 dle; //0x10
    uint8 scienceDataID;// 0x53
    uint8 dataLength;//calculated from the sizeof
    uint8 mainMajorV;//Major version of Main PSOC
    uint8 mainMinorV;//Minor version of Main PSOC
    uint8 mainHK[66];//Main housekeeping except header and footer
    uint8 eventHK[75];//Event housekeeping Packed date thru percent live time
    uint8 etx;//0x03
} LowRateHousekeeping;

LowRateHousekeeping lowRateHK;

/* Defines for DMA_LR_Cmd_1 */
//#define DMA_LR_Cmd_1_BYTES_PER_BURST 1
//#define DMA_LR_Cmd_1_REQUEST_PER_BURST 1
//#define DMA_LR_Cmd_1_SRC_BASE (CYDEV_PERIPH_BASE)
//#define DMA_LR_Cmd_1_DST_BASE (CYDEV_SRAM_BASE)
//#define DMA_LR_Cmd_1_BUFFER_SIZE 16
//uint8 buffCmdRxC[COMMAND_SOURCES][DMA_LR_Cmd_1_BUFFER_SIZE];
//reg16 * buffCmdRxCWritePtr[COMMAND_SOURCES];
//uint8 buffCmdRxCRead[COMMAND_SOURCES];
//
#define DMA_HR_Data_BYTES_PER_BURST 1
#define DMA_HR_Data_REQUEST_PER_BURST 1
#define DMA_HR_Data_SRC_BASE (CYDEV_SRAM_BASE)
#define DMA_HR_Data_DST_BASE (CYDEV_PERIPH_BASE)
#define DMA_HR_Data_BUFFER_SIZE 16
uint8 DMAHRDataChan = CY_DMA_INVALID_CHANNEL;
uint8 DMAHRDataTd = CY_DMA_INVALID_TD;
uint8 DMAHRDataActive = FALSE;

//const uint8 continueReadFlags = (SPIM_BP_STS_SPI_IDLE | SPIM_BP_STS_TX_FIFO_EMPTY);
volatile uint8 continueRead = FALSE;


//;AESOPLite Initialization Commands
//HiVol	FDB	$A735  ;T1 1431.6 High Voltage
//	FDB	$DD36  ;T2 1860.7
//	FDB	$CA37  ;T3 1704.7
//	FDB	$B9B5  ;T4 1553.3
//	FDB	$CB74  ;G  1706.8
//DiscP	FDB	$0039  ;Dual PHA card 0, All PHA Discriminators set to 7.0
//	FDB	$073A  ;T1
//	FDB	$0039  ;Dual PHA card 0
//	FDB	$0778  ;T2
//	FDB	$0139  ;Dual PHA card 1
//	FDB	$073A  ;T3
//	FDB	$0139  ;Dual PHA card 1
//	FDB	$0778  ;T4
//	FDB	$0239  ;Dual PHA card 2
//	FDB	$073A  ;G	
//	FDB	$0239  ;Dual PHA card 2
//	FDB	$0778  ;No Input
//DiscL	FDB	$0039  ;Dual PHA card 0, All Logic Discriminators set to 7.0
//	FDB	$073B  ;T1
//	FDB	$0039  ;Dual PHA card 0
//	FDB	$0779  ;T2
//	FDB	$0139  ;Dual PHA card 1
//	FDB	$073B  ;T3
//	FDB	$0139  ;Dual PHA card 1
//	FDB	$0779  ;T4
//	FDB	$0239  ;Dual PHA card 2
//	FDB	$073B  ;G
//	FDB	$0239  ;Dual PHA card 2
//	FDB	$0779  ;No Input
//Coinc	FDB	$F838  ;T1 T2 T3 Coincidence
//	FDB	$0AB7  ;10sec counter R/O
//	FDB	$0AB6  ;10sec Power R/O
//#define TESTTHRESHOLD 0x04 //Just for intializing T3 G DAC thresholds
//#define TESTTHRESHOLDT1 0x04 //Just for intializing T1 DAC thresholds
//#define TESTTHRESHOLDT4 0x03 //Just for intializing T4 DAC threshold

//AESOPLite Initialization Commands
#define NUMBER_INIT_CMDS	(38 + 83 + 5 + 6 + 0 + 1)//segments are divived by comments for easier counting
const uint8 initCmd[NUMBER_INIT_CMDS][2] = {
    //Event PSOC DAQ Trigger Setup
	{0x04, 0x23},  //Header for ToF DAC Threshold Set
	{0x01, 0x21},  //Channel ToF 1 
	{0x00, 0x22},  //DAC Byte MSB
	{0x20, 0x23},  //32 DAC Byte LSB
    {0x04, 0x23},  //Header for ToF DAC Threshold Set
	{0x02, 0x21},  //Channel ToF 2
	{0x00, 0x22},  //DAC Byte MSB
	{0x20, 0x23},  //32 DAC Byte LSB
    {0x01, 0x23},  //Header for DAC Threshold Set
	{0x05, 0x21},  //Channel 5 T2
	{0x00, 0x22},  //DAC Byte MSB
	{0x0F, 0x23},  //15 DAC Byte LSB
    {0x01, 0x22},  //Header for DAC Threshold Set
	{0x01, 0x21},  //Channel 1 G
	{0x06, 0x22},  //6 DAC Byte
    {0x01, 0x22},  //Header for DAC Threshold Set
	{0x02, 0x21},  //Channel 2 T3
	{0x06, 0x22},  //6 DAC Byte
    {0x01, 0x22},  //Header for DAC Threshold Set
	{0x03, 0x21},  //Channel 3 T1
	{0x0B, 0x22},  //11 DAC Byte
    {0x01, 0x22},  //Header for DAC Threshold Set
	{0x04, 0x21},  //Channel 4 T4
	{0x0A, 0x22},  //10 DAC Byte    
    {0x36, 0x22},  //Header for Trigger Mask Set
	{0x01, 0x21},  //1 Mask Primary 
	{0x02, 0x22},  //Trigger Mask 02 T1 T2 T4
    {0x36, 0x22},  //Header for Trigger Mask Set
    {0x02, 0x21},  //2 Mask Secondary 
	{0x06, 0x22},  //Trigger Mask 06 T1 T4
    {0x39, 0x22},  //Header for Trigger Prescale Set
    {0x01, 0x21},  //1 Tracker
	{0x04, 0x22},  //Prescale by 4 
    {0x39, 0x22},  //Header for Trigger Prescale Set
    {0x02, 0x21},  //2 PMT
	{0x01, 0x22},  //Prescale by 1     
//    {0x3A, 0x21},  //Header for Trigger Window Settling Time Set
//    {0x30, 0x21},  //Settling Time 48. Default 24 TODO Tune
//    {0x4B, 0x21},  //Header for Peak Detector Charge Time Set
//	{0x20, 0x21},  //32 cycle delay. Default 32 TODO Tune
    {0x4F, 0x21},  //Header for PMT Tracker Trigger Delay Set
	{0x0C, 0x21},  //12 cycle delay 
    //Event PSOC Tracker Setup
	{0x10, 0x23},  //Header for Tracker command
	{0x00, 0x21},  //0 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x01, 0x21},  //1 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x02, 0x21},  //2 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x03, 0x21},  //3 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x04, 0x21},  //4 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x05, 0x21},  //5 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x06, 0x21},  //6 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x07, 0x21},  //7 ID
	{0x04, 0x22},  //Reset FPGA
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x00, 0x21},  //0 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x01, 0x21},  //1 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x02, 0x21},  //2 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x03, 0x21},  //3 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x04, 0x21},  //4 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x05, 0x21},  //5 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x06, 0x21},  //6 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x23},  //Header for Tracker command
	{0x07, 0x21},  //7 ID
	{0x03, 0x22},  //Reset Config
	{0x00, 0x23},  //0 data bytes
    {0x10, 0x61},  //Header for Tracker command
	{0x00, 0x21},  //0 ID
	{0x06, 0x22},  //Set Trigger Delay
	{0x02, 0x23},  //2 data bytes
    {0x00, 0x60},  //0 Delay Cycles
    {0x00, 0x61},  //0 Stretch
    {0x59, 0xA0},  //Header for Tracker Layer Map command
	{0x02, 0x21},  //Tracker C
	{0x07, 0x22},  //Tracker H
	{0x01, 0x23},  //Tracker B
    {0x00, 0x60},  //Tracker A
    {0x04, 0x61},  //Tracker E
    {0x05, 0x62},  //Tracker F
    {0x06, 0x63},  //Tracker G
    {0x03, 0xA0},  //Tracker D
    {0x5B, 0x21},  //Header for Tracker Threshold Increase command. Only gets loaded by 0x56 command 
	{0x06, 0x21},  //Increase tracker threshold by 6
    {0x56, 0x21},  //Header for Tracker ASIC Power On & Config command. This command takes time so prefer not to issue an Event PSOC command after
	{0x08, 0x21},  //8 Layers. This command takes time so prefer not to issue an Event PSOC command after
    //HV Control Board Setup. Placed here to prevent Event PSOC command following 0x56 command 
	{0xAF, 0x35}, //T1 1500V High Voltage
	{0xCC, 0x36}, //T2 1718V High Voltage
	{0xC6, 0x37}, //T3 1671V High Voltage
	{0xBF, 0xB5}, //T4 1603V High Voltage
	{0xD1, 0x74}, //G  1757V High Voltage
    //Event PSOC Housekeeping Setup
    {0x57, 0x22},  //Header for Event PSOC Housekeeping command
	{0x05, 0x21},  //5 sec Rate
	{0x01, 0x22},  //1 Include Tracker Rate
    {0x5C, 0x21},  //Header for Event PSOC Tracker Housekeeping command
	{0x05, 0x21},  //5 min Rate
    {0x03, 0x20},  //Header For Read Errors. Init errors proir to this will be sent & cleared
	//Startup FPGA Input Timing Calibration
//    {0x48, 0x21},  //Header for FPGA Input Timing Calibration //obsolete in v100 tracker firmware
//	{0x08, 0x21},  //All FPGA. This command takes time so prefer not to issue an Event PSOC command after
    //Power Board Setup. Placed here to prevent a newly issued Event PSOC command from following 0x48 command 
	{0x0A, 0xB6},  //10sec Power R/O
    }; //End init cmds
#define CMD_BUFFER_SIZE 256 // max value for index since init commands is got longer than half buffer
#define CMD_MAIN_PSOC_ADDRESS 0b00101000 // Middle nibble of the second command byte is the address (0b1010 for Main PSOC, Event is 0b1000)
#define CMD_MAIN_FIRST_BYTE 0b00101001 // Middle nibble of the second command byte is the address (0b1010 for Main PSOC, Event is 0b1000)
#define CMD_ADDRESS_MASK 0b00111100 // Middle nibble of the second command byte mask for address
#define CMD_NUM_BYTE_MASK 0b11000011 // Outer nibble of the second command byte mask for number of bytes
uint8 buffCmd[COMMAND_SOURCES][CMD_BUFFER_SIZE][2];// circular buffer of commands from all sources 
uint8 readBuffCmd[COMMAND_SOURCES];//read indices for all command sources 
volatile uint8 writeBuffCmd[COMMAND_SOURCES];//write indices for all command sources
uint8 orderBuffCmd[COMMAND_SOURCES];//priority order for the command sources
uint8 headerBuffCmd[COMMAND_SOURCES];//Header of command being interpreted if any
uint8 interpretBuffCmd[COMMAND_SOURCES];//Next byte of command being interpreted if any
uint8 lastCmdSource = 0;//last command sources to send a command
volatile uint16 cntCmd = 0;//count of commands recieved (not sent)
uint8 cntCmdError = 0;//count of command errors
uint8 cntError = 0;//count of general errors

// Register pointers for the I2C chips
const uint8 INA226_Config_Reg = 0x00;
const uint8 INA226_ShuntV_Reg = 0x01;
const uint8 INA226_BusV_Reg = 0x02;
const uint8 INA226_Power_Reg = 0x03;
const uint8 INA226_Current_Reg = 0x04;
const uint8 INA226_Calib_Reg = 0x05;
const uint8 INA226_Mask_Reg = 0x06;
const uint8 INA226_Alert_Reg = 0x07;
const uint8 TMP100_Temp_Reg = 0x00;
const uint8 Barometer_Pres_Reg = 0xF7;
const uint8 Barometer_COE_PR11 = 0xA0;
const uint8 Barometer_COE_PTAT21 = 0xB1;


#define I2C_ADDRESS_TMP100 0x48
#define I2C_ADDRESS_BAROMETER 0x70
#define I2C_ADDRESS_RTC 0x6F
#define I2C_ADDRESS_INA226_3V_DIG 0x44
#define I2C_ADDRESS_INA226_3V_ANA 0x43
#define I2C_ADDRESS_INA226_5V_DIG 0x41
#define I2C_ADDRESS_INA226_5V_ANA 0x45
#define I2C_ADDRESS_INA226_15V_DIG 0x42
#define I2C_ADDRESS_INA226_TRACKER_SUPPLY 0x40//I2C Address 1000000 on Tracker power board
#define I2C_ADDRESS_INA226_TRACKER_BIAS 0x46//I2C Address 1000110 on Tracker power board

typedef struct I2CTrans {
	uint8 type;
    uint8 slaveAddress;
    uint8 * data;
    uint8 cnt;
    uint8 mode;
	uint8 error;
} I2CTrans;

#define I2C_BUFFER_SIZE (64u)
#define I2C_READ (1u)
#define I2C_WRITE (0u)
#define I2C_MAX_RETRIES (1u)
I2CTrans buffI2C[I2C_BUFFER_SIZE];
uint8 buffI2CRead, buffI2CWrite;
uint8 numI2CRetry = 0;

typedef struct HousekeepingTrackI2C {
    uint8 slaveAddress;
    uint8 regAddress;
    uint8 cnt;
    uint8 * data;
    uint8 writeTrans;
    uint8 readTrans;
} HousekeepingTrackI2C;

#define NO_WRITE_REG_ADDRESS (255u)
#define MAIN_HK_I2C_BUFFER_SIZE (14u)

HousekeepingTrackI2C mainHKI2C[MAIN_HK_I2C_BUFFER_SIZE]= {
{I2C_ADDRESS_BAROMETER, 0xF7, 6, NULL, 0, 0},//Barometer_Pres_Reg = 0xF7
{I2C_ADDRESS_TMP100, NO_WRITE_REG_ADDRESS, 2, NULL, 0, 0},//TMP100 defaults to read temp reg
{I2C_ADDRESS_INA226_3V_DIG, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_3V_DIG, 0x01, 2, NULL, 0, 0},//INA226_ShuntV_Reg = 0x01
{I2C_ADDRESS_INA226_3V_ANA, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_3V_ANA, 0x01, 2, NULL, 0, 0},//INA226_ShuntV_Reg = 0x01
{I2C_ADDRESS_INA226_5V_DIG, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_5V_DIG, 0x01, 2, NULL, 0, 0},//INA226_ShuntV_Reg = 0x01
{I2C_ADDRESS_INA226_5V_ANA, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_5V_ANA, 0x01, 2, NULL, 0, 0},//INA226_ShuntV_Reg = 0x01
{I2C_ADDRESS_INA226_15V_DIG, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_TRACKER_SUPPLY, 0x02, 2, NULL, 0, 0},//INA226_BusV_Reg = 0x02
{I2C_ADDRESS_INA226_TRACKER_SUPPLY, 0x01, 2, NULL, 0, 0},//INA226_ShuntV_Reg = 0x01
{I2C_ADDRESS_INA226_TRACKER_BIAS, 0x02, 2, NULL, 0, 0}};//INA226_BusV_Reg = 0x02

uint8 mainHKI2CRead = 0;

uint8 baroOnboardOTP[20];//storage for the OTP baro coefficients

RTC_Main_TIME_DATE mainTimeDate;// Structure for a local copy of RTC values, not updated by RTC
RTC_Main_TIME_DATE* mainTimeDateSysPtr;// Structure for a local copy of RTC values, not updated by RTC

uint8 rtcStatus; 
#define RTS_SET_MAIN        (0x01)
#define RTS_SET_I2C         (0x02)
#define RTS_SET_EVENT       (0x04)
#define RTS_SET_RPI         (0x08)
#define RTS_SET_MAIN_INP    (0x10)
#define RTS_SET_I2C_INP     (0x20)

#define DATA_RTS_I2C_BYTES   (8u)
uint8 dataRTCI2C[DATA_RTS_I2C_BYTES] = {
0x00, //Register addresss for seconds, start of trans
0x80, //Sec Register to init , MSb write starts clock
0x00, //Min Register
0x00, //Hour Register
0x09, //Day Register with Batt enable and Day 1
((MINOR_VERSION + 1) & 0x17), //Date Register, use version to produce a default value
(MAJOR_VERSION & 0x17), //Month Register, use version to produce a default value
0x00}; //Year Register


uint8 curRTSI2CTrans = I2C_BUFFER_SIZE;



typedef struct BaroCoeff {
	const double U0;
	const double Y1;
	const double Y2;
	const double Y3;
	const double C1;
	const double C2;
	const double C3;
	const double D1;
	const double D2;
	const double T1;
	const double T2;
	const double T3;
	const double T4;
	const double T5;
} BaroCoEff;

#define BARO_COUNT_TO_US (12)
#define NUM_BARO 2
#define NUM_BARO_CAPTURES 128//8
#define BARO_COUNT_MAX 0xFFFE //65534 is the max count on a 16 counter

uint16 buffBaroCap[NUM_BARO *2][NUM_BARO_CAPTURES];
uint8 buffBaroCapRead[NUM_BARO *2];
uint8 buffBaroCapWrite[NUM_BARO *2];
//DEBUG with num caps per isr 
//uint16 buffBaroCapNum[NUM_BARO *2][NUM_BARO_CAPTURES]; 
//uint8 buffBaroCapNumWrite;

volatile uint8 cntSecs = 0; //count 1 sec interrupts for housekeeping packet rates
uint8 hkSecs = 5; //# of secs per housekeeping packet
volatile uint8 hkReq = FALSE; //state to request packet 
uint8 hkCollecting = FALSE; //state to request packet 
volatile uint8 lowRateReq = FALSE; //state to request low rate science data packet 


//const BaroCoEff baroCE[NUM_BARO] = {{.U0 = 1.0, .Y1 = 1.0, .Y2 = 1.0, .Y3 = 1.0, .C1 = 1.0, .C2 = 1.0, .C3 = 1.0, .D1 = 1.0, .D2 = 1.0, .T1 = 1.0, .T2 = 1.0, .T3 = 1.0, .T4 = 1.0, .T5 = 1.0 }};
//const BaroCoEff baroCE[NUM_BARO] = {{.U0 = 5.875516, .Y1 = -3947.926, .Y2 = -10090.9, .Y3 = 0.0, .C1 = 95.4503, .C2 = 2.982818, .C3 = -135.3036, .D1 = 0.042247, .D2 = 0.0, .T1 = 27.91302, .T2 = 0.873949, .T3 = 21.00155, .T4 = 36.63574, .T5 = 0.0 }};
//double curBaroTemp[NUM_BARO];
//double curBaroPres[NUM_BARO];
uint32 curBaroTempCnt[NUM_BARO];
uint32 curBaroPresCnt[NUM_BARO];
uint32 baroReadReady = 0u;

int16 dieTemp;//temperature of the PSOC from system call

uint8 outputBusy = FALSE; //state for Pin_Busy, True when fram fifo queue is above a threshold
uint8 outputBusyHighThres = 80; //high threhold of fifo percentage
uint8 outputBusyLowThres = 70; //low threhold of fifo percentage

uint8 loopCount = 0;
uint8 loopCountCheck = 0;
#define SELECT_HIGH_LOOPS 250
//
//double BaroTempCalc ( double U, const BaroCoEff * bce )
//{
//	return (((bce->Y1) * U) + ((bce->Y2) * pow(U, 2))  + ((bce->Y3) * pow(U, 3)));
//}
//
//double BaroPresCalc ( double Tao, double U, const BaroCoEff * bce )
//{
//	double Usq = pow( U, 2);
//	double C = ((bce->C1) + ((bce->C2) * U) + ((bce->C3) * Usq)); 
//	double D = ((bce->D1) + ((bce->D2) * U)); 
//	double T0 = ((bce->T1) + ((bce->T2) * U) + ((bce->T3) * Usq) + ((bce->T4) * (U * Usq)) + ((bce->T5) * (Usq * Usq))); 
//	double ratio = (1 - (pow(T0, 2) / pow(Tao, 2)));
//	return ((C * ratio) * (1 - (D * ratio)));
//}

/*******************************************************************************
* Function Name: CmdBytes2String
********************************************************************************
*
* Summary:
*  Converts a 2 byte command in binary to a 4 byte ASCII representation of that 
*  command (null terminator is the 5th byte).  
*
* Parameters:
*  in:  uint8 pointer to 2 bytes to be converted 
*  out: uint8 pointer to 5 byte null terminted string of the result of 
*  2byte command converted to capitalized ASCII hexadecimal characters   
*  
* Return:
*  int number of charaters returned. Should be 4 on success, negative on fault
*
*******************************************************************************/
int CmdBytes2String (uint8* in, uint8* out)
{
    if ((NULL == in) || (NULL == (in + 1)) || (NULL == out)) //check for null pointers
    {
        cntError++;
        return -EFAULT; //null pointer error, sprint might also do this
    }
	return sprintf((char*)out, "%02X%02X", *(in), *(in + 1)); //converts the 2 bytes to hex with leading zerosv
}

uint8 BCD2Dec( uint8 bcd )
{
    return bcd - (6 * (bcd >> 4));
}
uint8 Dec2BCD( uint8 dec )
{
    uint16 num16 = dec;
    uint16 num8 = (uint8)((num16 * 103) >> 10);
    return dec + (6 * num8);
}

int SendCmdString (uint8 * in)
{
	if (0 != UART_Cmd_GetTxBufferSize()) return -EBUSY; // Not ready to send 
//	if (convert2Ascii) sprintf((char *)curCmd, "%x%x", (char)(*in), (char)*(in+1));
	for (uint8 x=0; x<3; x++)
	{
		UART_Cmd_PutArray(START_COMMAND, START_COMMAND_SIZE);
		UART_Cmd_PutArray(in, COMMAND_CHARS);
		UART_Cmd_PutArray(END_COMMAND, END_COMMAND_SIZE);
	}
	//Unix style line end
	UART_Cmd_PutChar(CR);
	UART_Cmd_PutChar(LF);
    //Debug
//    if (USBUART_CD_CDCIsReady())
//    {
//        *(in+4) = LF;
//        USBUART_CD_PutData(in, COMMAND_CHARS +1);
//
//    }
	return 0;
}

int SendInitCmds()
{
    if (CMD_BUFFER_SIZE <= (ACTIVELEN(readBuffCmd[0], writeBuffCmd[0], CMD_BUFFER_SIZE) + NUMBER_INIT_CMDS)) //check if space for commands
    {
        cntError++;
        return -ENOMEM;
    }
	uint8 tempNumCmdLeft = NUMBER_INIT_CMDS;
	uint8 tempNumCmdPart = 0;
    uint8 intState = CyEnterCriticalSection();
    uint8 tempWrite = writeBuffCmd[0];
    writeBuffCmd[0] = WRAP(writeBuffCmd[0] + NUMBER_INIT_CMDS, CMD_BUFFER_SIZE);
    CyExitCriticalSection(intState);
	if(CMD_BUFFER_SIZE <= (tempWrite + tempNumCmdLeft))
    {
        tempNumCmdPart = CMD_BUFFER_SIZE - tempWrite; //commands to end of buffer
        memcpy(&buffCmd[0][tempWrite][0], initCmd, (tempNumCmdPart * 2));// load all the init commands into 0 buffer
        tempNumCmdLeft -= tempNumCmdPart;//reduce commands left
        tempWrite = 0;//start begining of buffer
    }
    memcpy(&buffCmd[0][tempWrite][0], initCmd + (tempNumCmdPart * 2), (tempNumCmdLeft * 2));// load all the init commands into 0 buffer
    
    return NUMBER_INIT_CMDS;
}

int InitLRScienceData()
{
    lowRateHK.dle = DLE;
    lowRateHK.scienceDataID = SDATA_ID;
    lowRateHK.dataLength = sizeof(lowRateHK) - 4;//adapt to changing sizes, 4 formatting bytes not included 
    lowRateHK.mainMajorV = MAJOR_VERSION;//version to start, try to avoid confusion with LR events
    lowRateHK.mainMinorV = MINOR_VERSION;//version to start, try to avoid confusion with LR events
    lowRateHK.etx = ETX;
    return 1;
}

int CheckLRScienceData()
{

    if (lowRateReq)
    {
    
        //TODO event option
        if(0 == UART_LR_Data_GetTxBufferSize()) //Requests only come once every 30 Sec so if the buffer is not empty
        {
            uint8 curMainHK = WRAPDEC(buffHKWrite, HK_BUFFER_PACKETS); //the packet prior to the current write is most likely complete or blank        
            memcpy(lowRateHK.mainHK, buffHK[curMainHK].packedTimeDate, sizeof(lowRateHK.mainHK));//copy latest Main HK minus headers
            //TODO event HK needs to be copaaesied in CheckeEventPackets 
            UART_LR_Data_PutArray((uint8 *) &lowRateHK, sizeof(lowRateHK));
            lowRateReq = FALSE; //might need to make a critical section but the buffer in transmision should avoid duplicate sends.
            return 1;
        }
        else
        {
            lowRateReq = FALSE; //might need to make a critical section but the buffer in transmision should avoid duplicate sends.
            cntError++;
            return -EBUSY;
        }
    }
    return 0;
}

int ParseCmdInputByte(uint8 tempRx, uint8 i)
{
    switch(commandStatusC[i])
    {
        case WAIT_DLE:
            if (DLE == tempRx) commandStatusC[i] = CHECK_ID;
            break;
        case CHECK_ID:
            if (CMD_ID == tempRx) commandStatusC[i] = CHECK_LEN;
            else if (REQ_ID == tempRx) commandStatusC[i] = CHECK_ETX_REQ;
            else 
            {
                commandStatusC[i] = WAIT_DLE;
                cntCmdError++;
                return -EIDRM;
            }
            break;
        case CHECK_LEN:
            if(2 == tempRx){
                commandLenC[i] = tempRx;
                commandStatusC[i] = READ_CMD;
            }
            else 
            {
                commandStatusC[i] = WAIT_DLE;
                cntCmdError++;
                return -E2BIG;
            }
            break;
        case READ_CMD:
            if(commandLenC[i] > 0)
            {
                cmdRxC[i][commandLenC[i] % 2] = tempRx;
                commandLenC[i]--;
//                        buffUsbTxDebug[iBuffUsbTxDebug++] = commandLenC[i]; //debug
                if(0 == commandLenC[i])  commandStatusC[i]= CHECK_ETX_CMD;
            }
            
            break;
        case CHECK_ETX_CMD:
            if (ETX == tempRx)
            {
                
                int tempRes = CmdBytes2String(cmdRxC[i], curCmd);
                if(tempRes >= 0)
                {
//                    tempRes = SendCmdString(curCmd);  //TODO change this with considerations for commands like RTC set and duplicates
//                    if (-EBUSY == tempRes)
//                    {
                    uint8 intState = CyEnterCriticalSection();
                    uint8 tempWrite = writeBuffCmd[i];
                    writeBuffCmd[i] = WRAPINC(writeBuffCmd[i], CMD_BUFFER_SIZE);
                    CyExitCriticalSection(intState);
                    memcpy(buffCmd[i][tempWrite], cmdRxC[i], 2); //queue for later
                    cntCmd++;
                    lastCmdSource = i; //store last command source
//                    }
//                    else if (tempRes < 0)
//                    {
//                        //TODO Error handling
//                    }
                }
            }
            else 
            {
                cntCmdError++;
                //TODO error
                return -EILSEQ;
            }
            commandStatusC[i] = WAIT_DLE;
            break;
        case CHECK_ETX_REQ:
            if (ETX == tempRx)
            {
//                SendLRScienceData();
                lowRateReq = TRUE;
            }
            else 
            {
                cntCmdError++;
                //TODO error
                return -EILSEQ;
            }
            commandStatusC[i] = WAIT_DLE;
            break;
    }
    return 0;
}

//int CheckCmdDma(uint8 chanSrc)
//{
//   
//    uint8 tempRx;
//    int16 buffNewReadLen = *buffCmdRxCWritePtr[0] - LO16((uint32)buffCmdRxC[chanSrc]);
////    buffUsbTxDebug[iBuffUsbTxDebug++] = buffNewReadLen & 255; //debug
//    buffNewReadLen -= buffCmdRxCRead[chanSrc];
//    if (buffNewReadLen < 0) buffNewReadLen += DMA_LR_Cmd_1_BUFFER_SIZE;
////    buffUsbTxDebug[iBuffUsbTxDebug++] = buffNewReadLen & 255; //debug
//    
//    if(TRUE)
//    {
//        
//        while(buffNewReadLen-- > 1)   
//        {
//            buffUsbTxDebug[iBuffUsbTxDebug++] = buffNewReadLen & 255; //debug
//            buffCmdRxCRead[chanSrc] = WRAPINC(buffCmdRxCRead[chanSrc], DMA_LR_Cmd_1_BUFFER_SIZE);
//            tempRx = buffCmdRxC[chanSrc][buffCmdRxCRead[chanSrc]];  
//            buffUsbTxDebug[iBuffUsbTxDebug++] = tempRx; //debug
//            switch(commandStatusC[chanSrc])
//            {
//                case WAIT_DLE:
//                    if (DLE == tempRx) commandStatusC[chanSrc] = CHECK_ID;
//                    break;
//                case CHECK_ID:
//                    if (CMD_ID == tempRx) commandStatusC[chanSrc] = CHECK_LEN;
//                    if (REQ_ID == tempRx) commandStatusC[chanSrc] = CHECK_ETX_REQ;
//                    break;
//                case CHECK_LEN:
//                    if(2 == tempRx){
//                        commandLenC[chanSrc] = tempRx;
//                        commandStatusC[chanSrc] = READ_CMD;
//                    }
//                    else commandStatusC[chanSrc] = WAIT_DLE;
//                    break;
//                case READ_CMD:
//                    if(commandLenC[0] > 0)
//                    {
//                        cmdRxC[chanSrc][commandLenC[chanSrc] % 2] = tempRx;
//                        commandLenC[0]--;
////                        buffUsbTxDebug[iBuffUsbTxDebug++] = commandLenC[0]; //debug
//                        if(0 == commandLenC[chanSrc])  commandStatusC[chanSrc]= CHECK_ETX_CMD;
//                    }
//                    
//                    break;
//                case CHECK_ETX_CMD:
//                    if (ETX == tempRx)
//                    {
//                        
//                        int tempRes = CmdBytes2String(cmdRxC[chanSrc], curCmd);
//                        if(tempRes >= 0)
//                        {
//                            tempRes = SendCmdString(curCmd);  
//                            if (-EBUSY == tempRes)
//                            {
//                                memcpy(buffCmd[chanSrc][writeBuffCmd[chanSrc]], cmdRxC[chanSrc], 2); //busy queue for later
//                                writeBuffCmd[chanSrc] = WRAPINC(writeBuffCmd[chanSrc], CMD_BUFFER_SIZE);
//                            }
//                            else if (tempRes < 0)
//                            {
//                                //TODO Error handling
//                            }
//                        }
//                    }
//                    else 
//                    {
//                        //TODO error
//                    }
//                    commandStatusC[chanSrc] = WAIT_DLE;
//                    break;
//                case CHECK_ETX_REQ:
//                    if (ETX == tempRx)
//                    {    
//                        SendLRScienceData();
//                    }
//                    break;
//            }
//                
//        }
//    }
//    return 0;
//}

int CheckCmdBuffers()
{
    if (0 != UART_Cmd_GetTxBufferSize()) return -EBUSY; // Not ready to send
    uint8 curChan;
    for (uint8 i = 0; i < COMMAND_SOURCES; i++) 
    {
        curChan = orderBuffCmd[i];
        if (readBuffCmd[curChan] != writeBuffCmd[curChan]) // check if q has cmd
        {
            int tempRes = CmdBytes2String(buffCmd[curChan][readBuffCmd[curChan]], curCmd);
            tempRes = SendCmdString(curCmd);
            readBuffCmd[curChan] = WRAPINC(readBuffCmd[curChan], CMD_BUFFER_SIZE);
            return 1;
        }
    }
    return 0;
}

int InterpretCmdBuffers()
{
    uint8 search4Cmd = TRUE, i = 0;
    uint8 curChan = orderBuffCmd[i];
    uint8 lastAdr;
    do //search for 1 command for the main PSOC, only interpreting 1 per main program loop
    {
        if(headerBuffCmd[curChan] == writeBuffCmd[curChan])
        {
            i++;
            if(i < COMMAND_SOURCES)
            {
                curChan = orderBuffCmd[i];
            }
            else 
            {
                return 0; //nothing to interpret
            }
        }
        else
        {
            uint8 headAdr;
            if(headerBuffCmd[curChan] == interpretBuffCmd[curChan])
            {
                headAdr = buffCmd[curChan][headerBuffCmd[curChan]][1];
                interpretBuffCmd[curChan] = WRAPINC(interpretBuffCmd[curChan], CMD_BUFFER_SIZE);
                if (CMD_MAIN_PSOC_ADDRESS == (headAdr & CMD_ADDRESS_MASK))
                {
                    if (0 == (headAdr & CMD_NUM_BYTE_MASK))
                    {
                        search4Cmd = FALSE;
                    }
                    else
                    {
                        lastAdr = headAdr;
                    }
                }
                else
                {
                    headerBuffCmd[curChan] = WRAPINC(headerBuffCmd[curChan], CMD_BUFFER_SIZE);
                    return 0; //everytime a header changes return & check next time
                }
            }
            else
            {
                lastAdr = buffCmd[curChan][WRAPDEC(interpretBuffCmd[curChan], CMD_BUFFER_SIZE)][1];
                headAdr = buffCmd[curChan][headerBuffCmd[curChan]][1];
            }
            while (TRUE == search4Cmd)
            {
                if (interpretBuffCmd[curChan] == writeBuffCmd[curChan])
                {
                    i++;
                    if(i < COMMAND_SOURCES)
                    {
                        curChan = orderBuffCmd[i];
                    }
                    else 
                    {
                        return 0; //nothing to interpret
                    }
                    break; //check next availiable channel in outer while loop
                }
                uint8 curAdr =  buffCmd[curChan][interpretBuffCmd[curChan]][1];
                if(curAdr == headAdr) //end of multibyte command
                {
                    uint8 numDataBytes = ACTIVELEN(headerBuffCmd[curChan], interpretBuffCmd[curChan], CMD_BUFFER_SIZE);
                    numDataBytes = ((numDataBytes & 0xC) << 4) | (numDataBytes & 3); //shifted to outer nibble
                    if ( numDataBytes == ( CMD_ADDRESS_MASK & headAdr ))
                    {
                        search4Cmd = FALSE;
                    }
                    else
                    {
                        headerBuffCmd[curChan] = interpretBuffCmd[curChan];
                        cntCmdError++;
                        return -EILSEQ;
                    }
                }
                else if (lastAdr == headAdr)
                {
                    if (CMD_MAIN_FIRST_BYTE == curAdr)
                    {
                        lastAdr = curAdr; //byte inc correctly 
                        interpretBuffCmd[curChan] = WRAPINC(interpretBuffCmd[curChan], CMD_BUFFER_SIZE);
                    }
                    else
                    {
                        headerBuffCmd[curChan] = interpretBuffCmd[curChan];
                        cntCmdError++;
                        return -EILSEQ;
                    }
                }
                else
                {
                    uint8 curAdrDiff = curAdr - lastAdr;
                    switch (curAdrDiff)
                    {
                        case 1:
                            break;
                        case 29: 
                            if(3 == (lastAdr & 3))
                            {
                                break;//byte increment skipping middle address nibble
                            }
                        default:
                            headerBuffCmd[curChan] = interpretBuffCmd[curChan];
                            cntCmdError++;
                            return -EILSEQ;
                    }
                    lastAdr = curAdr; //byte inc correctly 
                    interpretBuffCmd[curChan] = WRAPINC(interpretBuffCmd[curChan], CMD_BUFFER_SIZE);
                }
            }
        }
            
    }while(TRUE == search4Cmd);
    
    uint8 cmdID = buffCmd[curChan][headerBuffCmd[curChan]][0];
    switch(cmdID)
    {
        default:
            headerBuffCmd[curChan] = WRAPINC(interpretBuffCmd[curChan], CMD_BUFFER_SIZE);
            interpretBuffCmd[curChan] = headerBuffCmd[curChan];
    }
    return 0;
}

uint8 CheckI2C()
{
	if( buffI2CRead != buffI2CWrite)  //Check if any transactions
	{
        uint8 status;

        status = I2C_RTC_MasterStatus();
        if( 0 == (status & I2C_RTC_MSTAT_XFER_INP )) //Check if busy
        {

            uint8 errors;
            errors = (status & I2C_RTC_MSTAT_ERR_MASK);

            //TODO handle completion and errors
            if( errors != 0)
            {
                buffI2C[buffI2CRead].error = errors;
                buffI2CRead = WRAPINC(buffI2CRead, I2C_BUFFER_SIZE);
                numI2CRetry = 0;
                cntError++;
            }
            else if ( 0 != (status & I2C_RTC_MSTAT_RD_CMPLT ))
            {
                if(I2C_READ ==  buffI2C[buffI2CRead].type)
                {
                    buffI2C[buffI2CRead].error = 0;  
                }
                else 
                {
                    buffI2C[buffI2CRead].error = I2C_RTC_MSTAT_ERR_MASK; //TODO new Error for thei mismatch
                    cntError++;
                }
                buffI2CRead = WRAPINC(buffI2CRead, I2C_BUFFER_SIZE);
                numI2CRetry = 0;
            }
            else if ( 0 != (status & I2C_RTC_MSTAT_WR_CMPLT ))
            {
                if(I2C_WRITE ==  buffI2C[buffI2CRead].type)
                {
                    buffI2C[buffI2CRead].error = 0;  
                }
                else 
                {
                    buffI2C[buffI2CRead].error = I2C_RTC_MSTAT_ERR_MASK; //TODO new Error for thei mismatch
                    cntError++;
                }
                buffI2CRead = WRAPINC(buffI2CRead, I2C_BUFFER_SIZE);
                numI2CRetry = 0;
            }
            else //execute new transacttion
            {
                if(I2C_WRITE ==  buffI2C[buffI2CRead].type)
                {
                    errors = I2C_RTC_MasterWriteBuf(buffI2C[buffI2CRead].slaveAddress, buffI2C[buffI2CRead].data, buffI2C[buffI2CRead].cnt, buffI2C[buffI2CRead].mode);
                    if (0 != errors)
                    {
                        cntError++;
                        //TODO handle individual errors
                        numI2CRetry++;
                    }
                }
                else if(I2C_READ ==  buffI2C[buffI2CRead].type)
                {
                    errors = I2C_RTC_MasterReadBuf(buffI2C[buffI2CRead].slaveAddress, buffI2C[buffI2CRead].data, buffI2C[buffI2CRead].cnt, buffI2C[buffI2CRead].mode);
                    if (0 != errors)
                    {
                        cntError++;
                        //TODO handle individual errors
                        numI2CRetry++;
                    }
                }
                if (I2C_MAX_RETRIES <= numI2CRetry)
                {
                    buffI2C[buffI2CRead].error = errors;
                    buffI2CRead = WRAPINC(buffI2CRead, I2C_BUFFER_SIZE);
                    numI2CRetry = 0;
                }
            }
        }
        I2C_RTC_MasterClearStatus();
    }
    
    return 0;
}

FmBufferIndex InitFrameBuffer()
{
    FmBufferIndex initFB = 0;
    while (FRAME_BUFFER_SIZE > initFB)
    {
        buffFrameData[initFB].seqL = (uint8)(initFB & 0xFF); //seqL is the LSB of the index of the Frame Buffer and doesn't need to change
        memcpy(buffFrameData[initFB].sync, frameSync, 2);
        memcpy((buffFrameData[initFB].sync + 2), frameSync, 2);
        initFB++;
        
    }
    return initFB;
}

const uint8 ForcedSampleBaroI2CBytes[2] = {0xF4, 0xFD}; //F4 is CTRL_MEAS register address. In FD 01 lsb is forcedmode, rest 1s 64 avg for both temp and pressure

int8 ForcedSampleBaroI2C()
{
    if(I2C_BUFFER_SIZE > (2 + ACTIVELEN(buffI2CRead, buffI2CWrite, I2C_BUFFER_SIZE)))
    {
        buffI2C[buffI2CWrite].type = I2C_WRITE;//need to write to reg to force sample
        buffI2C[buffI2CWrite].slaveAddress = I2C_ADDRESS_BAROMETER;
        buffI2C[buffI2CWrite].cnt = 2;
        buffI2C[buffI2CWrite].data = ForcedSampleBaroI2CBytes;//register then value to force samp
        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
                    
        return 1;
    }
    else
    {
        return -EBUSY;
    }
}

int8 InitBaroI2COTP()//get OTP coeffienct to adjust the raw outputs on the GSE 
{
     if(I2C_BUFFER_SIZE > (5 + ACTIVELEN(buffI2CRead, buffI2CWrite, I2C_BUFFER_SIZE)))
    {
        
        
        buffI2C[buffI2CWrite].type = I2C_WRITE;//need to write to reg 
        buffI2C[buffI2CWrite].slaveAddress = I2C_ADDRESS_BAROMETER;
        buffI2C[buffI2CWrite].cnt = 1;//reg byte address
        buffI2C[buffI2CWrite].data = &Barometer_COE_PR11;//data points to the register number
//        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_NO_STOP;
        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
        
        buffI2C[buffI2CWrite].type = I2C_READ;//need to read the OTP
        buffI2C[buffI2CWrite].slaveAddress = I2C_ADDRESS_BAROMETER;
        buffI2C[buffI2CWrite].cnt = 16;//16 is first set of OTP
        buffI2C[buffI2CWrite].data = baroOnboardOTP;//data pointer to start of OTP storage
        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
        
        buffI2C[buffI2CWrite].type = I2C_WRITE;//need to write to reg
        buffI2C[buffI2CWrite].slaveAddress = I2C_ADDRESS_BAROMETER;
        buffI2C[buffI2CWrite].cnt = 1;//reg byte address
        buffI2C[buffI2CWrite].data = &Barometer_COE_PTAT21;//data points to the register number
//        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_NO_STOP;
        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
        
        buffI2C[buffI2CWrite].type = I2C_READ;//need to read the OTP
        buffI2C[buffI2CWrite].slaveAddress = I2C_ADDRESS_BAROMETER;
        buffI2C[buffI2CWrite].cnt = 4;//4  more OTP
        buffI2C[buffI2CWrite].data = (baroOnboardOTP + 16);//data pointer to rest of OTP storage
        buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
        
        return 1;
    }
    else
    {
        return -EBUSY;
    }
}


uint8 InitRTC()
{
//    mainTimeDate = RTC_Main_ReadTime(); //TODO dont write to the read loactiion, create temp structure
//    RTC_Main_TIME_DATE mainTimeDateTemp; //create temp structure
    mainTimeDate.Sec = 0;
    mainTimeDate.Min = 0;
    mainTimeDate.Hour = 0;
    mainTimeDate.DayOfWeek = 1; //0 is not valid and WriteTime doesn't modify this
    mainTimeDate.DayOfMonth = MAJOR_VERSION % 30;
    mainTimeDate.DayOfYear = MAJOR_VERSION % 30;
    mainTimeDate.Month = 1;
    mainTimeDate.Year = MINOR_VERSION;
    RTC_Main_WriteTime(&mainTimeDate);
    RTC_Main_Start();
    return mainTimeDate.Year;
}
uint8 InitHKBuffer()
{
    uint8 initHK = 0;
    while (HK_BUFFER_PACKETS > initHK)
    {
        buffHK[initHK].header[0] = HK_HEAD;
        memcpy(buffHK[initHK].header + 1, frame00FF, 2);
//        buffHK[initHK].version[0] = MAJOR_VERSION;
//        buffHK[initHK].version[1] = MINOR_VERSION;
        buffHK[initHK].EOR[0] = EOR_HEAD;
        memcpy(buffHK[initHK].EOR + 1, frame00FF, 2);
//        memset(buffHK[initHK].padding, 0, HK_PAD_SIZE);
        initHK++;
        
    }
    return initHK;
}

uint8 CheckHKBuffer()
{
    if (TRUE == hkCollecting) //see if collecting is done
    {
        
        uint8 continueCheck = TRUE;
        do
        {
            if( I2C_BUFFER_SIZE == mainHKI2C[mainHKI2CRead].readTrans ) //if set to this there re no more transactions
            {
                mainHKI2CRead = MAIN_HK_I2C_BUFFER_SIZE;
                continueCheck = FALSE;
            }
            else if( ISELEMENTDONE(mainHKI2C[mainHKI2CRead].readTrans, buffI2CRead, buffI2CWrite) )// checck if transaction done
            {
                
            
                if(buffI2C[mainHKI2C[mainHKI2CRead].readTrans].error )
                {
                    memset(mainHKI2C[mainHKI2CRead].data, 0, mainHKI2C[mainHKI2CRead].cnt);//0 values since errors
                    
                    buffHK[buffHKWrite].missingValuesThisPacket++;
                }
                else if(I2C_BUFFER_SIZE != mainHKI2C[mainHKI2CRead].writeTrans)
                {
                    if(buffI2C[mainHKI2C[mainHKI2CRead].writeTrans].error )
                    {
                        memset(mainHKI2C[mainHKI2CRead].data, 0, mainHKI2C[mainHKI2CRead].cnt);//0 values since errors
                        
                        buffHK[buffHKWrite].missingValuesThisPacket++;
                    }
                }
                mainHKI2CRead++;
                
            }
            else 
            {
                continueCheck = FALSE;// wait for I2c
            }
            if (MAIN_HK_I2C_BUFFER_SIZE <= mainHKI2CRead)
            {
                memcpy(buffHK[buffHKWrite].commandLast, buffCmd[lastCmdSource][WRAPDEC(writeBuffCmd[lastCmdSource], CMD_BUFFER_SIZE)], 2); //copy the last command recieved 
                uint32 temp32 = cntCmd;
                buffHK[buffHKWrite].commandCount[1] = temp32 & 0xFF; //LSB of command count
                temp32 >>= 8;
                buffHK[buffHKWrite].commandCount[0] = temp32 & 0xFF; //MSB of command count
                buffHK[buffHKWrite].commandErrors = cntCmdError;
                buffHK[buffHKWrite].generalErrors = cntError;
                temp32 = ACTIVELEN(buffFrameDataRead, buffFrameDataWrite, FRAME_BUFFER_SIZE) * 100;
                temp32 /= FRAME_BUFFER_SIZE;
                buffHK[buffHKWrite].fifoPercentFull = temp32 & 0xFF;
                if ((TRUE == outputBusy) && (outputBusyLowThres >= buffHK[buffHKWrite].fifoPercentFull))
                {
                    outputBusy = FALSE;
                    Pin_Busy_Write(outputBusy);// no longer signal busy
                }
                else if ((FALSE == outputBusy) && (outputBusyHighThres <= buffHK[buffHKWrite].fifoPercentFull))
                {
                    outputBusy = TRUE;
                    Pin_Busy_Write(outputBusy);//signal busy
                }
                temp32 = cntFramesDropped;
                buffHK[buffHKWrite].framesDroppedRS232[1] = temp32 & 0xFF; //LSB of Dropped RS232 packets
                temp32 >>= 8;
                buffHK[buffHKWrite].framesDroppedRS232[0] = temp32 & 0xFF; //MSB of Dropped RS232 packets
                temp32 = cntFramesDroppedUSB;
                buffHK[buffHKWrite].framesDroppedUSB[1] = temp32 & 0xFF; //LSB of Dropped USB packets
                temp32 >>= 8;
                buffHK[buffHKWrite].framesDroppedUSB[0] = temp32 & 0xFF; //MSB of Dropped USB packets
                if  (CYRET_SUCCESS == DieTemp_Main_Query(&dieTemp))
                {
                    int16 temp16 = dieTemp; //signed 16 bit from -40 to 140
                    buffHK[buffHKWrite].coreDieTemp[1] = temp16 & 0xFF; //LSB of core temp
                    temp16 >>= 8;
                    buffHK[buffHKWrite].coreDieTemp[0] = temp16 & 0xFF; //MSB of core temp
                }
                else
                {
                    buffHK[buffHKWrite].missingValuesThisPacket++;
                    buffHK[buffHKWrite].coreDieTemp[0] = 0x80; //MSB of core temp, Max negative number is out-of-range error indicator 
                    buffHK[buffHKWrite].coreDieTemp[1] = 0x00; //LSB of core temp
                    cntError++;// TODO could check specific error
                }
                buffHK[buffHKWrite].generalErrors = cntError;
                buffHKWrite = WRAPINC( buffHKWrite , HK_BUFFER_PACKETS );
                hkCollecting = FALSE;
                ForcedSampleBaroI2C(); //Force sample next Baro
                return 1;
            }
        }while(continueCheck);
        
    }
    else if ((TRUE == hkReq)) //see if req is made by ISRCheckBaro
    {
        hkCollecting = TRUE;
        uint8 intState = CyEnterCriticalSection();
        hkReq = FALSE;
        CyExitCriticalSection(intState);
        //start specific data collection
//        uint32 temp32 = curBaroTempCnt[0];
////        int8 i=2; //24bit for Counter1 style packet DEBUG
//        int8 i=3; //32bit 
//        buffHK[buffHKWrite].baroTemp1[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
//        while (0 <= --i) //Fill the Higher order bytes
//        {
//            temp32 >>= 8;
//            buffHK[buffHKWrite].baroTemp1[i] = temp32 & 0xFF;
//        }
//        temp32 = curBaroPresCnt[0];
//      i=3; //32bit
////        i=2; //24bit for Counter1 style packet DEBUG
//        buffHK[buffHKWrite].baroPres1[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
//        while (0 <= --i) //Fill the Higher order bytes
//        {
//            temp32 >>= 8;
//            buffHK[buffHKWrite].baroPres1[i] = temp32 & 0xFF;
//        }
//        temp32 = curBaroTempCnt[1];
//        i=3; //32bit
////        i=2; //24bit for Counter1 style packet DEBUG
//        buffHK[buffHKWrite].baroTemp2[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
//        while (0 <= --i) //Fill the Higher order bytes
//        {
//            temp32 >>= 8;
//            buffHK[buffHKWrite].baroTemp2[i] = temp32 & 0xFF;
//        }
//        temp32 = curBaroPresCnt[1];
//        i=3; //32bit
////        i=2; //24bit for Counter1 style packet DEBUG
//        buffHK[buffHKWrite].baroPres2[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
//        while (0 <= --i) //Fill the Higher order bytes
//        {
//            temp32 >>= 8;
//            buffHK[buffHKWrite].baroPres2[i] = temp32 & 0xFF;
//        }
//        RTC_Main_DisableInt();
//        mainTimeDateSysPtr = RTC_Main_ReadTime();
//        memcpy(&mainTimeDate, mainTimeDateSysPtr, sizeof(mainTimeDate));// copy to local struct before update
//        RTC_Main_EnableInt();
        
//        temp32 = (uint32)(mainTimeDate.Year % 2000) << 4;
//        temp32 |= mainTimeDate.Month;
//        temp32 <<= 5;//shift left to make room for new bits;
//        temp32 |= mainTimeDate.DayOfMonth;
//        temp32 <<= 5;//shift left to make room for new bits;
//        temp32 |= mainTimeDate.Hour;
//        temp32 <<= 6;//shift left to make room for new bits;
//        temp32 |= mainTimeDate.Min;
//        temp32 <<= 6;//shift left to make room for new bits;
//        temp32 |= mainTimeDate.Sec;
//        
////        temp32 = 60 * ( ( 60 * mainTimeDate.Hour) + mainTimeDate.Min ) + mainTimeDate.Sec; // Convert RTC to secs
//        i=3; //32bit
////        i=2; //24bit for Counter1 style packet DEBUG
//        buffHK[buffHKWrite].packedTimeDate[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
//        while (0 <= --i) //Fill the Higher order bytes
//        {
//            temp32 >>= 8;
//            buffHK[buffHKWrite].packedTimeDate[i] = temp32 & 0xFF;
//        }
        
//        uint8 buffBaroCapNumWriteTemp = buffBaroCapNumWrite; //DEBUG
//        if (buffBaroCapNumWriteTemp )
//        {
//            buffBaroCapNumWriteTemp--;
//        }
//        else 
//        {
//            buffBaroCapNumWriteTemp = NUM_BARO_CAPTURES - 1;
//        }
//        if ((0 != buffBaroCapNum[0][buffBaroCapNumWriteTemp]) && (buffBaroCapNum[0][buffBaroCapNumWriteTemp] == buffBaroCapNum[1][buffBaroCapNumWriteTemp])  && (buffBaroCapNum[2][buffBaroCapNumWriteTemp] == buffBaroCapNum[3][buffBaroCapNumWriteTemp])) buffHK[buffHKWrite].padding[0]=1;//DEBUG
//        Pin_CE1_Write(buffHK[buffHKWrite].secs[3] % 2); //DEBUG timing on scope
        
        //load the data pointer of each
        mainHKI2C[0].data = buffHK[buffHKWrite].baroPres3;//I2C Address 1110000
        mainHKI2C[1].data = buffHK[buffHKWrite].boardTemperature;//I2C Address 1001000
        mainHKI2C[2].data = buffHK[buffHKWrite].digital3VVoltage;//I2C Address 1000100
        mainHKI2C[3].data = buffHK[buffHKWrite].digital3VAmperage;//I2C Address 1000100
        mainHKI2C[4].data = buffHK[buffHKWrite].analog3VVoltage;//I2C Address 1000011
        mainHKI2C[5].data = buffHK[buffHKWrite].analog3VAmperage;//I2C Address 1000011
        mainHKI2C[6].data = buffHK[buffHKWrite].digital5VVoltage;//I2C Address 1000001
        mainHKI2C[7].data = buffHK[buffHKWrite].digital5VAmperage;//I2C Address 1000001
        mainHKI2C[8].data = buffHK[buffHKWrite].analog5VVoltage;//I2C Address 1000101
        mainHKI2C[9].data = buffHK[buffHKWrite].analog5VAmperage;//I2C Address 1000101
        mainHKI2C[10].data = buffHK[buffHKWrite].digital15VVoltage;//I2C Address 1000010
        mainHKI2C[11].data = buffHK[buffHKWrite].trackerVoltage;//I2C Address 1000000
        mainHKI2C[12].data = buffHK[buffHKWrite].trackerAmperage;//I2C Address 1000000
        mainHKI2C[13].data = buffHK[buffHKWrite].trackerBiasVoltage;//I2C Address 1000110
        mainHKI2CRead = 0; //start from begining of i2c tracker
        uint8 fullI2CTrans = FALSE;
        for (uint8 curI2C = 0; curI2C < MAIN_HK_I2C_BUFFER_SIZE; curI2C++)//create all i2c transations
        {
            if(fullI2CTrans)
            {
                mainHKI2C[curI2C].writeTrans = I2C_BUFFER_SIZE; //buffer full so don't attempt this i2c 
                mainHKI2C[curI2C].readTrans = I2C_BUFFER_SIZE; //buffer full so don't attempt this i2c
                buffHK[buffHKWrite].missingValuesThisPacket++;
            }
            else
            {
                if(I2C_BUFFER_SIZE <= (3 + ACTIVELEN(buffI2CRead, buffI2CWrite, I2C_BUFFER_SIZE)))
                {
                    mainHKI2C[curI2C].writeTrans = I2C_BUFFER_SIZE; //buffer full so don't attempt this i2c 
                    mainHKI2C[curI2C].readTrans = I2C_BUFFER_SIZE; //buffer full so don't attempt this i2c
                    buffHK[buffHKWrite].missingValuesThisPacket++;
                    fullI2CTrans = TRUE;
                }
                else
                {
                    if(NO_WRITE_REG_ADDRESS == mainHKI2C[curI2C].regAddress)
                    {
                        mainHKI2C[curI2C].writeTrans = I2C_BUFFER_SIZE; //no need to write reg pointer 
                        
                    }
                    else
                    {
                        mainHKI2C[curI2C].writeTrans = buffI2CWrite;//index so can check results
                        buffI2C[buffI2CWrite].type = I2C_WRITE;//need to write the register pointer
                        buffI2C[buffI2CWrite].slaveAddress = mainHKI2C[curI2C].slaveAddress;
                        buffI2C[buffI2CWrite].cnt = 1;// only 1 byte
                        buffI2C[buffI2CWrite].data = &(mainHKI2C[curI2C].regAddress);//data points to the register number
//                        if (2 > curI2C) //DEBUG Baro and Temp I2C do not want stops
//                        {
//                            buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_NO_STOP;
//                            
//                        }
//                        else 
//                        {
                            buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
//                        }
                        buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
                        
                    }
                    mainHKI2C[curI2C].readTrans = buffI2CWrite;//index so can check results
                    buffI2C[buffI2CWrite].type = I2C_READ;//need to read the values
                    buffI2C[buffI2CWrite].slaveAddress = mainHKI2C[curI2C].slaveAddress;
                    buffI2C[buffI2CWrite].cnt = mainHKI2C[curI2C].cnt;//spefic number of bytes to readout
                    buffI2C[buffI2CWrite].data = mainHKI2C[curI2C].data;//data pointer
                    buffI2C[buffI2CWrite].mode = I2C_RTC_MODE_COMPLETE_XFER;
                    
                    buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
                }
                
            }
            
            
        }
        DieTemp_Main_Start();//start the temp conversion and Query the result at that end of HK. TODO could check error returns but handled at Query for now
        buffHK[buffHKWrite].missingValuesThisPacket = 0;
       
    }
    return 0;
}



#define EV_DUMP_SIZE (EV_BUFFER_SIZE - WRAP(EV_BUFFER_SIZE, FRAME_DATA_BYTES))
#define EV_MIN_SIZE (9u)
#define EV_MAX_SIZE (255u + 9u) //max 1 byte len + addtional bytes
int8 CheckEventPackets()
{
    if ((buffEvWriteLast != buffEvWrite) && (buffEvRead != buffEvWrite) && ((WRAPINC(packetEvTail, PACKET_EVENT_SIZE) != packetEvHead))) //check for new active data in event buffer, and no overflow
    {
        EvBufferIndex curRead = buffEvRead;
        buffEvWriteLast = buffEvWrite;
        if (packetEvHead != packetEvTail) //check for queued packets to decide where to start
        {
            curRead = WRAPINC( packetEv[ WRAPDEC(packetEvTail, PACKET_EVENT_SIZE) ].EOR , EV_BUFFER_SIZE); //move active past last packet found
        }
        EvBufferIndex startRead = curRead; //store the largest search bound for comparison later 
//        EvBufferIndex curEOR = WRAPDEC(buffEvWrite, EV_BUFFER_SIZE);
        EvBufferIndex nBytes = ACTIVELEN(curRead, buffEvWrite, EV_BUFFER_SIZE);
        if (EV_DUMP_SIZE <= nBytes)
        {
            uint8 tmpPacketEvTail = packetEvTail;
            packetEvTail = WRAPINC(packetEvTail, PACKET_EVENT_SIZE);
            packetEv[tmpPacketEvTail].header = curRead;
            packetEv[tmpPacketEvTail].EOR = WRAP( curRead + (EV_DUMP_SIZE - 1), EV_BUFFER_SIZE); // inclusive so -1 to the dump size
            
            return 1;
        }
        EvBufferIndex curEOR = WRAPDEC(buffEvWrite, EV_BUFFER_SIZE);// make inclusive
        while (EV_MIN_SIZE <= nBytes) //min packet size is smallest search space
        {
            if(frame00FF[1] == buffEv[curEOR])
            {
                EvBufferIndex iterRev = WRAPDEC(curEOR, EV_BUFFER_SIZE); //iterator to check prev bytes
                if(frame00FF[0] == buffEv[iterRev])
                {
                    
                    if(EOR_HEAD == buffEv[ WRAPDEC(iterRev, EV_BUFFER_SIZE)]) //last 3 bytes should be EOR 0xFF00FF
                    {
                        
                        EvBufferIndex expBytes = ACTIVELEN(curRead, curEOR, EV_BUFFER_SIZE) + 1; //expected bytes to check packet structure, +1 inclusive
                        iterRev = WRAP(expBytes, 3); //calc number of bytes off 3 byte alignment and temp store in iterRev (done with EOR checks)
                        if (0 != iterRev) //check if misaligned search space
                        {
//                            iterRev = (3 - iterRev); //calc number of bytes needed to get on 3 byte alignment
                            if (iterRev < expBytes)//prevent underflow
                            {
                                expBytes -= iterRev; //reduce byte expectation to 3 byte alignment
//                                nBytes -= iterRev; //reduce num byte to 3 byte alignment
                                curRead = WRAP( curRead + iterRev, EV_BUFFER_SIZE); //move read into 3 byte alignment
                            }
                        }
                        if (EV_MAX_SIZE < expBytes)
                        {
                            curRead = WRAP( (EV_BUFFER_SIZE - EV_MAX_SIZE) + 1 + curEOR, EV_BUFFER_SIZE);//max search space for header, + 1 inclusive
                            expBytes = EV_MAX_SIZE; // now expecting the max size packet, will keep reducing by 3
//                            nBytes = EV_MAX_SIZE; // now expecting the max size packet, will keep reducing by 3
                        }
                        while (EV_MIN_SIZE <= expBytes) //min packet size is smallest search space
                        {
                            EvBufferIndex calcBytes = EV_MIN_SIZE; //data bytes in fixed packet, excludes header & EOR
                            switch (buffEv[curRead])
                            {
                                case EVVAR_HEAD:
                                    calcBytes = buffEv[ WRAP3INC(curRead, EV_BUFFER_SIZE)] + 9u;// valid data bytes in packet, might not be multiple of 3. Add for header, EOR, & len
                                case EVFIX_HEAD: //EVVAR_HEAD continues here
                                    if (((expBytes - 2u) <= calcBytes) && ((expBytes) >= calcBytes)) //3 byte range for the listed len compared to actual
                                    {
                                        EvBufferIndex iterFwd = WRAPINC( curRead, EV_BUFFER_SIZE); //iterator to check next bytes
                                        if(frame00FF[0] == buffEv[iterFwd])
                                        {
                                            if(frame00FF[1] == buffEv[WRAPINC( iterFwd, EV_BUFFER_SIZE)]) //header is in curRead position, packet location and bookend checked
                                            {
                                                uint8  numPkts = 0;
//                                                uint8 intState = CyEnterCriticalSection(); //TODO consider the mutex
                                                if (curRead != startRead)// check if data that failed checks precededs the header
                                                {
                                                    uint8 tmpPacketEvTail = packetEvTail;
                                                    packetEvTail = WRAPINC(packetEvTail, PACKET_EVENT_SIZE); //dumping the unchecked data
                                                    packetEv[tmpPacketEvTail].header = startRead; //start with beginning of active bytes
                                                    packetEv[tmpPacketEvTail].EOR = WRAPDEC( curRead , EV_BUFFER_SIZE); // 1 byte before Read ends dump
                                                    numPkts++;
                                                }
//                                                CyExitCriticalSection(intState); //TODO consider the mutex
                                                if ((WRAPINC(packetEvTail, PACKET_EVENT_SIZE) != packetEvHead)) //check if space for another packet
                                                {
                                                    uint8 tmpPacketEvTail = packetEvTail;
                                                    packetEvTail = WRAPINC(packetEvTail, PACKET_EVENT_SIZE); //dumping the unchecked data
                                                    packetEv[tmpPacketEvTail].header = curRead; //start with found header
                                                    packetEv[tmpPacketEvTail].EOR = curEOR; // found EOR
                                                    numPkts++;
                                                }
                                                return numPkts;
                                            }
                                        }
                                    }
                                    break;
                            }
                            expBytes -= 3; //shrink search space by 3
                            curRead = WRAP3INC(curRead, EV_BUFFER_SIZE); //move forward along 3 byte alignment
                        }
                        return 0; // give up after first potential EOR found to limit loop time (stay order n). will dump this out eventually & will processed by a PC (more CPU & time)
                    }
                }
            }
           
            nBytes--; //shrink search space
            curEOR = WRAPDEC(curEOR, EV_BUFFER_SIZE); //Move back to check next byte
//            nBytes = ACTIVELEN(curRead, curEOR, EV_BUFFER_SIZE) + 1; //shrink search space to new endpoints, +1 inclusive
            
        }
        
        
    }
    return 0;
}

int8 CheckFrameBuffer()
{
	
    if (buffFrameDataWrite != buffFrameDataRead)
    {
        uint8 tempRes;
        switch (DMAHRDataActive)
        {
            case TRUE:
                
                tempRes = Status_Reg_UART_DMA_Read(); //check for nrq from finished DMA
                if(0 == (tempRes & 0x1)) break; //no nrq so exit 
                buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE); //nrq indincates DMA finished 
                if (buffFrameDataWrite == buffFrameDataRead)
                {
                    DMAHRDataActive = FALSE; //nothing left in buffer
                    break;
                }
            case FALSE:
                DMAHRDataActive = TRUE; //indicate that DMA is starting up
                if (DMA_INVALID_TD != DMAHRDataTd) //Check for old TD
                {
                    CyDmaTdFree(DMAHRDataTd); //free old TD
                    
                }
                DMAHRDataTd = CyDmaTdAllocate(); //allocate new TD
                
                CyDmaTdSetConfiguration(DMAHRDataTd, (sizeof(FrameOutput) - 1), DMA_DISABLE_TD, (CY_DMA_TD_INC_SRC_ADR | DMA_HR_Data__TD_TERMOUT_EN)); // transfer frame 1 byte at time except the first byte

                CyDmaTdSetAddress(DMAHRDataTd, LO16((uint32)&(buffFrameData[ buffFrameDataRead ].seqM)), LO16((uint32)UART_HR_Data_TXDATA_PTR));// Set Source and Destination address

                CyDmaChSetInitialTd(DMAHRDataChan, DMAHRDataTd);//TD initialization
        
                tempRes = UART_HR_Data_ReadTxStatus(); //clear any pending interrupts
                CyDmaClearPendingDrq(DMAHRDataTd);//clear in case there is already a drq
                UART_HR_Data_PutChar((buffFrameData[ buffFrameDataRead ].seqH)); //start UART with first byte DMA will get rest
                CyDmaChEnable(DMAHRDataChan, 0u);//Enable the DMA channel    
                
        }
            
//        if (UART_HR_Data_GetTxBufferSize() <= 0)
//        if ((UART_HR_Data_GetTxBufferSize() <= 0) && (0 != (UART_HR_Data_ReadTxStatus() & UART_HR_Data_TX_STS_FIFO_EMPTY  ) ))
//        {
////            UART_HR_Data_PutArray((uint8*)&(buffFrameData[ buffFrameDataRead ]) , sizeof(FrameOutput));
//            buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
//            
//        }
    }
    
    if (buffFrameDataWrite != buffFrameDataReadUSB)
    {
        if ((0u != USBUART_CD_GetConfiguration()) )
        {
        

            if (USBUART_CD_CDCIsReady())
            {
                USBUART_CD_PutData((uint8*)&(buffFrameData[ buffFrameDataReadUSB ]), sizeof(FrameOutput));
//                memcpy( (buffUsbTx + iBuffUsbTx), (uint8*)&(buffFrameData[ buffFrameDataReadUSB ]), sizeof(FrameOutput));
//    			iBuffUsbTx += sizeof(FrameOutput);
                buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
            }
        }
    }
    if (packetEvHead != packetEvTail) //check if queued Event packets, Top Priority will starve others if new one every loop
    {
        EvBufferIndex curRead = packetEv[ packetEvHead ].header;
		EvBufferIndex curEOR = packetEv[ packetEvHead ].EOR;
        EvBufferIndex nDataBytesLeft = ACTIVELEN(curRead, curEOR, EV_BUFFER_SIZE) + 1;
        EvBufferIndex nDataBytesLeftLR = 0;//used for both HK and Event copy if packet meets criteria
        EvBufferIndex nBytes = 0;
        uint8 tmpWrite  = 0;
        uint8 tmpWriteLR  = 0;//where to copy in the Low Rate packet
		packetEvHead = WRAPINC(packetEvHead, PACKET_EVENT_SIZE);
        buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
        buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
        if (COPY_EVENT_HK == eventLRCopy) //check if LR is set to HK
        {
            if (EVHK_ID == buffEv[WRAP(curRead + 4, EV_BUFFER_SIZE)])//4 byte offset from headeris ID byte
            {
                nDataBytesLeftLR = nDataBytesLeft - 3; //don't copy the 3 byte EOR
            }
        }
//        seqFrame2HB++;
        while(0 < nDataBytesLeft)
		{
			nBytes = MIN(FRAME_DATA_BYTES - tmpWrite, nDataBytesLeft);
			if (curEOR < curRead)
			{
				nBytes = MIN(EV_BUFFER_SIZE - curRead, nBytes);
			}
            
			memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), (buffEv + curRead), nBytes);

            if (0 < nDataBytesLeftLR) //try to copy to Low Rate as well
            {
                if (COPY_EVENT_HK == eventLRCopy) //check if LR is set to HK
                {
                    uint8 lowRateOffset = 0; //might need to offset the start of the copy to needed data
                    if( sizeof(lowRateHK.eventHK) < nDataBytesLeftLR )
                    {
                        lowRateOffset = nDataBytesLeftLR - sizeof(lowRateHK.eventHK); //calculate staring offset
                    }
                    if (nBytes > lowRateOffset) //check if needed data to copy
                    {
                        uint8 nBytesLR = MIN(nBytes, nDataBytesLeftLR);
			            memcpy( (void*) ( (lowRateHK.eventHK) + tmpWriteLR ), (buffEv + curRead + lowRateOffset), (nBytesLR - lowRateOffset)); //copy data past the offset 
                        tmpWriteLR += (nBytesLR - lowRateOffset);
                        nDataBytesLeftLR -= nBytesLR;
                    }
                    else
                    {
                        nDataBytesLeftLR -= nBytes;
                    }
                }
            }
                
            
			nDataBytesLeft -= nBytes;
			curRead += (nBytes - 1); //avoiding overflow with - 1 , will add later
//			if (curRead == curEOR)
//			{
//                packetEvHead = WRAPINC(packetEvHead, PACKET_EVENT_SIZE);
//                //Could add next packet to the frame but not preferred at the moment
//
//			}
			if (curRead >= (EV_BUFFER_SIZE - 1))
			{
				curRead = buffEvRead = 0;
//				curRead = 0;
			}
			else
			{
                curRead = WRAPINC(curRead, EV_BUFFER_SIZE); //last increment, handling the wrap
				buffEvRead = curRead;
			}
            tmpWrite += nBytes;
            
            if (FRAME_DATA_BYTES <= tmpWrite)
            {
                if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
                {
                    seqFrame2HB++;
                }
                buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
                if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
                {
                    buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                    cntFramesDropped++;
                }
                if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
                {
                    buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                    cntFramesDroppedUSB++;
                }
                buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
                buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
               
                tmpWrite = 0;
            }
		}
		
		if ((FRAME_DATA_BYTES > tmpWrite) && (0 < tmpWrite))
		{
            uint8 bytesAlign = WRAP(tmpWrite, 3); //calc number of bytes off 3 byte alignment and temp store in iterRev (done with EOR checks)
            if (0 != bytesAlign) //check if misaligned search space
            {
                buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                if (1 == bytesAlign)// needs 2nd padding byte
                {
                    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                }
            }
            while (FRAME_DATA_BYTES > tmpWrite)
            {
			    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = NULL_HEAD;
                memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), frame00FF, 2);
                tmpWrite += 2;
			}
		    if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
            {
                seqFrame2HB++;
            }
            buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
            if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
            {
                buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                cntFramesDropped++;
            }
            if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
            {
                buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                cntFramesDroppedUSB++;
            }
        }
    }
    else if (packetFIFOHead != packetFIFOTail) //check if queued Backplane packets
    {
		uint8 curSPIDev = packetFIFO[packetFIFOHead].index;
        SPIBufferIndex curRead = packetFIFO[ packetFIFOHead ].header;
		SPIBufferIndex curEOR = packetFIFO[ packetFIFOHead ].EOR;
        SPIBufferIndex nDataBytesLeft = ACTIVELEN(curRead, curEOR, SPI_BUFFER_SIZE) + 1;
        SPIBufferIndex nBytes = 0;
        uint8 tmpWrite  = 0;
		packetFIFOHead = WRAPINC(packetFIFOHead, PACKET_FIFO_SIZE);
        buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
        buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
//        seqFrame2HB++;
        while(nDataBytesLeft > 0)
		{
            nBytes = MIN(FRAME_DATA_BYTES - tmpWrite, nDataBytesLeft);
			if (curEOR < curRead)
			{
				nBytes = MIN(SPI_BUFFER_SIZE - curRead, nBytes);
			}
			// if (curEOR < curRead)
			// {
			// 	nBytes = MIN(SPI_BUFFER_SIZE - curRead, nDataBytesLeft);
			// }
            // else
            // {
            //     nBytes = nDataBytesLeft;
            // }
			// nBytes = MIN(FRAME_DATA_BYTES - tmpWrite, nBytes);
//			nBytes = MIN(FRAME_DATA_BYTES - tmpWrite, nDataBytesLeft);
            
			memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), (void*) &(buffSPI[curSPIDev] [ curRead ]), nBytes);

			nDataBytesLeft -= nBytes;
			curRead += (nBytes - 1); //avoiding overflow with - 1 , will add later
//			if (curRead == curEOR)
//			{
//                packetEvHead = WRAPINC(packetEvHead, PACKET_EVENT_SIZE);
//                //Could add next packet to the frame but not preferred at the moment
//
//			}
			if (curRead >= (SPI_BUFFER_SIZE - 1))
			{
				curRead = buffSPIRead[curSPIDev] = 0;
			}
			else
			{
                curRead = WRAPINC(curRead, SPI_BUFFER_SIZE); //last increment, handling the wrap
				buffSPIRead[curSPIDev] = curRead;
			}
            tmpWrite += nBytes;

            if (FRAME_DATA_BYTES <= tmpWrite)
            {
                if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
                {
                    seqFrame2HB++;
                }
                buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
                if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
                {
                    buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                    cntFramesDropped++;
                }
                if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
                {
                    buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                    cntFramesDroppedUSB++;
                }
                buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
                buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
               
                tmpWrite = 0;
            }
		}
		
		if ((FRAME_DATA_BYTES > tmpWrite) && (0 < tmpWrite))
		{
            uint8 bytesAlign = WRAP(tmpWrite, 3); //calc number of bytes off 3 byte alignment and temp store in iterRev (done with EOR checks)
            if (0 != bytesAlign) //check if misaligned search space
            {
                buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                if (1 == bytesAlign)// needs 2nd padding byte
                {
                    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                }
            }
            while (FRAME_DATA_BYTES > tmpWrite)
            {
			    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = NULL_HEAD;
                memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), frame00FF, 2);
                tmpWrite += 2;
			}
            if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
            {
                seqFrame2HB++;
            }
            buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
            if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
            {
                buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                cntFramesDropped++;
            }
            if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
            {
                buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                cntFramesDroppedUSB++;
            }
        }
    }
    else if (buffHKRead != buffHKWrite) //check if queued Housekeeping packets
    {
        uint8 curRead = 0;
        uint8 nDataBytesLeft = sizeof(HousekeepingPeriodic);
        uint8 nBytes = 0;
        uint8 tmpWrite  = 0;
        buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
        buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
//        seqFrame2HB++;
        while(nDataBytesLeft > 0)
		{

			nBytes = MIN(FRAME_DATA_BYTES - tmpWrite, nDataBytesLeft);
//            void* addHK = (void*)(&(buffHK[buffHKRead]))  + curRead; //DEBUG

//			memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), (&(buffHK[buffHKRead])  + curRead), nBytes);
//			memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), (addHK), nBytes);// DEBUG
			memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), (void*)(&(buffHK[buffHKRead]))  + curRead, nBytes);

			nDataBytesLeft -= nBytes;
			curRead += nBytes;
            tmpWrite += nBytes;
           
            if (FRAME_DATA_BYTES <= tmpWrite)
            {
                if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
                {
                    seqFrame2HB++;
                }
                buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
                if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
                {
                    buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                    cntFramesDropped++;
                }
                if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
                {
                    buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                    cntFramesDroppedUSB++;
                }
                buffFrameData[ buffFrameDataWrite ].seqM =  seqFrame2HB & 0xFF; //middle seqence byte
                buffFrameData[ buffFrameDataWrite ].seqH =  seqFrame2HB >> 8; //high seqence byte
               
                tmpWrite = 0;
            }
		}
		
		if ((FRAME_DATA_BYTES > tmpWrite) && (0 < tmpWrite))
		{
            uint8 bytesAlign = WRAP(tmpWrite, 3); //calc number of bytes off 3 byte alignment and temp store in iterRev (done with EOR checks)
            if (0 != bytesAlign) //check if misaligned search space
            {
                buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                if (1 == bytesAlign)// needs 2nd padding byte
                {
                    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = 0x00; //add padding byte to fix alignment
                }
            }
            while (FRAME_DATA_BYTES > tmpWrite)
            {
			    buffFrameData[ buffFrameDataWrite ].data[ tmpWrite++ ] = NULL_HEAD;
                memcpy( (void*) &(buffFrameData[ buffFrameDataWrite ].data[ tmpWrite ]), frame00FF, 2);
                tmpWrite += 2;
			}
            if((255) == buffFrameData[ buffFrameDataWrite ].seqL )
            {
                seqFrame2HB++;
            }
            buffFrameDataWrite = WRAPINC(buffFrameDataWrite, FRAME_BUFFER_SIZE);
            if (buffFrameDataWrite == buffFrameDataRead) //Overwrite and drop RS232 frame
            {
                buffFrameDataRead = WRAPINC(buffFrameDataRead, FRAME_BUFFER_SIZE);
                cntFramesDropped++;
            }
            if (buffFrameDataWrite == buffFrameDataReadUSB) //Overwrite and drop USB frame
            {
                buffFrameDataReadUSB = WRAPINC(buffFrameDataReadUSB, FRAME_BUFFER_SIZE);
                cntFramesDroppedUSB++;
            }
    		buffHKRead = WRAPINC(buffHKRead, HK_BUFFER_PACKETS);
        }
    }
    
    
    return 0;
}

uint8 CheckRTC()
{
    if (0 != (rtcStatus & RTS_SET_MAIN_INP))
    {
        uint8 curRTSI2CTrans2 = WRAPINC(curRTSI2CTrans, I2C_BUFFER_SIZE);
        if ( (0 != buffI2C[curRTSI2CTrans].error) && ( ISELEMENTDONE(curRTSI2CTrans, buffI2CRead, buffI2CWrite)))
        {
            cntError++;
            //TODO error handling
//            rtcStatus |= RTS_SET_MAIN; //Retry forever DEBUG
            rtcStatus ^= RTS_SET_MAIN_INP;
        }
        else if (ISELEMENTDONE(curRTSI2CTrans2, buffI2CRead, buffI2CWrite))
        {
            if (0 != buffI2C[curRTSI2CTrans2].error)
            {
                cntError++;
                //TODO error handling
//                rtcStatus |= RTS_SET_MAIN; //Retry forever DEBUG
                rtcStatus ^= RTS_SET_MAIN_INP;
            }   
            else
            {
                mainTimeDate.Sec = BCD2Dec(dataRTCI2C[1] & 0x7F);
                mainTimeDate.Min = BCD2Dec(dataRTCI2C[2] & 0x7F);
                mainTimeDate.Hour = BCD2Dec(dataRTCI2C[3] & 0x3F);
//                mainTimeDate.DayOfWeek = (dataRTCI2C[4] & 0x07); //0 is not valid and WriteTime doesn't modify this
                mainTimeDate.DayOfMonth = BCD2Dec(dataRTCI2C[5] & 0x3F);
                mainTimeDate.Month = BCD2Dec(dataRTCI2C[6] & 0x1F);
                mainTimeDate.Year = BCD2Dec(dataRTCI2C[7]) + 2000;
                RTC_Main_WriteTime(&mainTimeDate);
                rtcStatus ^= RTS_SET_MAIN_INP;
            }
        }
    }
    else if (0 != (rtcStatus & RTS_SET_I2C_INP))
    {
        if ( ISELEMENTDONE(curRTSI2CTrans, buffI2CRead, buffI2CWrite))
        {
            if (0 != buffI2C[curRTSI2CTrans].error)
            {
                cntError++;
                //TODO error handling
                rtcStatus |= RTS_SET_I2C; //Retry  forever DEBUG
            }
            rtcStatus ^= RTS_SET_I2C_INP;
        }
    }
    else if (0 != (rtcStatus & RTS_SET_MAIN))
    {
        if(I2C_BUFFER_SIZE > (3 + ACTIVELEN(buffI2CRead, buffI2CWrite, I2C_BUFFER_SIZE)))
        {
            curRTSI2CTrans = buffI2CWrite;
            buffI2CWrite = WRAP(buffI2CWrite + 2, I2C_BUFFER_SIZE);
            
            buffI2C[curRTSI2CTrans].type = I2C_WRITE;
            buffI2C[curRTSI2CTrans].slaveAddress = I2C_ADDRESS_RTC;
            buffI2C[curRTSI2CTrans].data = dataRTCI2C;
            buffI2C[curRTSI2CTrans].cnt = 1;
            buffI2C[curRTSI2CTrans].mode = I2C_RTC_MODE_COMPLETE_XFER;
    //        buffI2C[curRTSI2CTrans].mode = I2C_RTC_MODE_NO_STOP;
            
            uint8 curRTSI2CTrans2 = WRAPINC(curRTSI2CTrans, I2C_BUFFER_SIZE);
            buffI2C[curRTSI2CTrans2].type = I2C_READ;
            buffI2C[curRTSI2CTrans2].slaveAddress = I2C_ADDRESS_RTC;
            buffI2C[curRTSI2CTrans2].data = (dataRTCI2C + 1); //0 element is register address to write
            buffI2C[curRTSI2CTrans2].cnt = 7;
            buffI2C[curRTSI2CTrans2].mode = I2C_RTC_MODE_COMPLETE_XFER;
            rtcStatus |= RTS_SET_MAIN_INP;
            rtcStatus ^= RTS_SET_MAIN;
        }
    }
    else if (0 != (rtcStatus & RTS_SET_I2C))
    {
        if(I2C_BUFFER_SIZE > (2 + ACTIVELEN(buffI2CRead, buffI2CWrite, I2C_BUFFER_SIZE)))
        {
            curRTSI2CTrans = buffI2CWrite;
            buffI2CWrite = WRAPINC(buffI2CWrite, I2C_BUFFER_SIZE);
            
            RTC_Main_DisableInt();
            mainTimeDateSysPtr = RTC_Main_ReadTime();
            memcpy(&mainTimeDate, mainTimeDateSysPtr, sizeof(mainTimeDate));// make local copy before changes
            RTC_Main_EnableInt();
            
            dataRTCI2C[1] = (Dec2BCD(mainTimeDate.Sec) & 0x7F) | 0x80; //0x80 enables Oscillator
            dataRTCI2C[2] = Dec2BCD(mainTimeDate.Min) & 0x7F;
            dataRTCI2C[3] = Dec2BCD(mainTimeDate.Hour) & 0x3F;
            dataRTCI2C[4] = (Dec2BCD(mainTimeDate.DayOfWeek - 1) & 0x07) | 0x08; //DayOfWeek starts at 1. 0x08 enables external battery
            dataRTCI2C[5] = Dec2BCD(mainTimeDate.DayOfMonth) & 0x3F;
            dataRTCI2C[6] = Dec2BCD(mainTimeDate.Month) & 0x1F;
            dataRTCI2C[7] = Dec2BCD((uint8)(mainTimeDate.Year % 100));
            
            buffI2C[curRTSI2CTrans].type = I2C_WRITE;
            buffI2C[curRTSI2CTrans].slaveAddress = I2C_ADDRESS_RTC;
            buffI2C[curRTSI2CTrans].data = dataRTCI2C;
            buffI2C[curRTSI2CTrans].cnt = 8;
            buffI2C[curRTSI2CTrans].mode = I2C_RTC_MODE_COMPLETE_XFER;
            
            rtcStatus |= RTS_SET_I2C_INP;
            rtcStatus ^= RTS_SET_I2C;
        }
    }
    else if (0 != (rtcStatus & RTS_SET_EVENT))
    {
        uint8 tmpOrder = orderBuffCmd[0];
        if (CMD_BUFFER_SIZE <= (ACTIVELEN(readBuffCmd[tmpOrder], writeBuffCmd[tmpOrder], CMD_BUFFER_SIZE) + 11)) //check if space for commands
        {
            cntError++;
            //TODO errr log
            return -ENOMEM;
        }
        //TOD0 check that this doesn't pass read index in the command buffer
        uint8 intState = CyEnterCriticalSection();
        uint8 tmpWrite = writeBuffCmd[tmpOrder];
        writeBuffCmd[tmpOrder] = WRAP(writeBuffCmd[tmpOrder] + 11, CMD_BUFFER_SIZE);
        CyExitCriticalSection(intState);
        RTC_Main_DisableInt();
        mainTimeDateSysPtr = RTC_Main_ReadTime();
        memcpy(&mainTimeDate, mainTimeDateSysPtr, sizeof(mainTimeDate));// make local copy before changes
        RTC_Main_EnableInt();
        buffCmd[tmpOrder][tmpWrite][0] = 0x45; //Set RTC command
        buffCmd[tmpOrder][tmpWrite][1] = 0xA2; //8 Address, 10 bytes
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.Sec; //Sec
        buffCmd[tmpOrder][tmpWrite][1] = 0x21; //byte #1
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.Min; //Min
        buffCmd[tmpOrder][tmpWrite][1] = 0x22; //byte #2
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.Hour; //Hour
        buffCmd[tmpOrder][tmpWrite][1] = 0x23; //byte #3
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.DayOfWeek; //DayOfWeek
        buffCmd[tmpOrder][tmpWrite][1] = 0x60; //byte #4
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.DayOfMonth; //DayOfMonth
        buffCmd[tmpOrder][tmpWrite][1] = 0x61; //byte #5
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = *((uint8*)(((uint8*) &(mainTimeDate.DayOfYear)) + 1)); //DayOfYear MSB Little endian to Big endian conversion in the precomplier
        buffCmd[tmpOrder][tmpWrite][1] = 0x62; //byte #6
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = *((uint8*) &(mainTimeDate.DayOfYear)); //DayOfYear LSB Little endian to Big endian conversion in the precomplier
        buffCmd[tmpOrder][tmpWrite][1] = 0x63; //byte #7
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = mainTimeDate.Month; //DayOfMonth
        buffCmd[tmpOrder][tmpWrite][1] = 0xA0; //byte #8
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = *((uint8*)(((uint8*) &(mainTimeDate.Year)) + 1)); //DayOfYear MSB Little endian to Big endian conversion in the precomplier
        buffCmd[tmpOrder][tmpWrite][1] = 0xA1; //byte #9
        tmpWrite = WRAPINC(tmpWrite, CMD_BUFFER_SIZE);
        buffCmd[tmpOrder][tmpWrite][0] = *((uint8*) &(mainTimeDate.Year)); //DayOfYear LSB Little endian to Big endian conversion in the precomplier
        buffCmd[tmpOrder][tmpWrite][1] = 0xA2; //byte #10

        rtcStatus ^= RTS_SET_EVENT;
    }
    else if (0 != (rtcStatus & RTS_SET_RPI))
    {
    
        //TODO Rpi commands
        
        rtcStatus ^= RTS_SET_RPI;
    }
    return 0;
}

CY_ISR(ISRCheckCmd)
{
    uint8 intState = CyEnterCriticalSection();
    uint8 tempStatus1 = UART_LR_Cmd_1_ReadRxStatus();
    uint8 tempStatus2 = UART_LR_Cmd_2_ReadRxStatus();
    uint8 tempRx;
    uint8 i = 0;
//    buffUsbTxDebug[iBuffUsbTxDebug++] = UART_LR_Cmd_1_GetRxBufferSize(); //debug
    if((tempStatus1 | UART_LR_Cmd_1_RX_STS_FIFO_NOTEMPTY) > 0)
    {
        
        while(UART_LR_Cmd_1_GetRxBufferSize())   
        {
            int tempRes = ParseCmdInputByte(UART_LR_Cmd_1_ReadRxData(), i);
            if (0 > tempRes)
            {
                //TODO error handling additional
            }
            
                
        }
    }
    
    i=1;
    if((tempStatus1 | UART_LR_Cmd_2_RX_STS_FIFO_NOTEMPTY) > 0)
    {
        
        while(UART_LR_Cmd_2_GetRxBufferSize())   
        {
            int tempRes = ParseCmdInputByte(UART_LR_Cmd_2_ReadRxData(), i);
            if (0 > tempRes)
            {
                //TODO error handling additional
            }
            
                
        }
    
    }
    
    CyExitCriticalSection(intState);
}

CY_ISR(ISRReadSPI)
{
//	if (iCmdBuff < CMDBUFFSIZE - 1)
//	{
//		SPIM_BP_WriteTxData(cmdBuff[iCmdBuff++]);
//	}
//	else if (!Pin_nDrdy_Read())
//	{
//		iCmdBuff = CMDBUFFSIZE - 1;
//		SPIM_BP_WriteTxData(cmdBuff[iCmdBuff]);
//	}
//	uint8 tempStatus = SPIM_BP_ReadStatus();
	uint8 intState = CyEnterCriticalSection();

	uint8 tempnDrdy = Pin_nDrdy_Filter_Read();
	SPIBufferIndex tempBuffWrite = buffSPIWrite[iSPIDev];
//	uint8 tempStatus = SPIM_BP_ReadStatus();
	uint8 tempStatus = SPIM_BP_ReadTxStatus();
//	Control_Reg_LoadPulse_Write(0x01);
    (*tabSPISel[iSPIDev])(0u);//select low for a period of time
    Timer_SelLow_Start();
    continueRead = TRUE;
	if (tempBuffWrite != buffSPICurHead[iSPIDev]) //Check if buffer is full
	{
		buffSPIWrite[iSPIDev] = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
		 //if ((0u == Pin_nDrdy_Read()) && (0u != (SPIM_BP_TX_STATUS_REG & SPIM_BP_STS_TX_FIFO_EMPTY)) && (buffSPIWrite[iSPIDev] != buffSPIRead[iSPIDev]))
//	    uint8 tempnDrdy = Pin_nDrdy_Filter_Read(); //placed here in hopes the glith filter can change to 1 at end of data
		if ((0u != tempnDrdy) || ((WRAP3INC(buffSPIWrite[iSPIDev], SPI_BUFFER_SIZE)) == buffSPIRead[iSPIDev]))
//		if ((buffSPIWrite[iSPIDev] == buffSPIRead[iSPIDev]))
		{
			continueRead = FALSE;
//			Control_Reg_CD_Write(0x00u);
//			SPIM_BP_ClearTxBuffer();
		}
//		else 
//		{
//			Control_Reg_CD_Write(0x02u);
//			Timer_SelLow_Start();
//			if (0u != (SPIM_BP_STS_TX_FIFO_EMPTY & tempStatus))
//			{
//				SPIM_BP_WriteTxData(FILLBYTE);
//			}
//		}
//		tempStatus = SPIM_BP_ReadStatus();
		tempStatus = SPIM_BP_ReadRxStatus(); //need to check RxStatus before ReadRxData()
		if (0u != (SPIM_BP_STS_RX_FIFO_NOT_EMPTY & tempStatus))
		{
			buffSPI[iSPIDev][tempBuffWrite] = SPIM_BP_ReadRxData();
		}
	   
		
	}
	else 
	{
        cntError++;
        //TODO Error hadling
//		Control_Reg_CD_Write(0x00u);
        continueRead = FALSE;
//		SPIM_BP_ClearTxBuffer();
//		tempStatus = SPIM_BP_ReadStatus();
	}
	
	CyExitCriticalSection(intState);
}
CY_ISR(ISRWriteSPI)
{
    uint8 intState = CyEnterCriticalSection();
	uint8 tempStatus = Timer_SelLow_ReadStatusRegister();
//	if (0u != (SPIM_BP_STS_TX_FIFO_EMPTY & SPIM_BP_TX_STATUS_REG))
//	{
//		SPIM_BP_WriteTxData(FILLBYTE);
//	}
//    (*tabSPISel[iSPIDev])(1u);//select high to check the selected board
    if(continueRead)
    {
        Control_Reg_LoadPulse_Write(0x01);
        SPIM_BP_WriteTxData(FILLBYTE);
        (*tabSPISel[iSPIDev])(1u);//select high to check the selected board
//        Control_Reg_CD_Write(0x02u);

    }
//    else
//    {
//        Control_Reg_CD_Write(0x00u);
//    }
//	if(0u != (Timer_SelLow_ReadControlRegister() & Timer_SelLow_CTRL_ENABLE ))
//	{
    Timer_SelLow_Stop();
//	}
    CyExitCriticalSection(intState);
}
CY_ISR(ISRReadEv)
{
	uint8 intState = CyEnterCriticalSection(); //TODO consider the mutex
	EvBufferIndex tempBuffWrite = buffEvWrite;
	uint8 tempStatus = SPIS_Ev_ReadStatus();
	if (0u != (SPIS_Ev_STS_RX_BUF_NOT_EMPTY & tempStatus)) 
	{
        buffEv[tempBuffWrite] = SPIS_Ev_ReadRxData();
		tempBuffWrite = WRAPINC(tempBuffWrite, EV_BUFFER_SIZE);
        if (tempBuffWrite == buffEvRead) buffEvRead = WRAPINC(tempBuffWrite, EV_BUFFER_SIZE); //Discard oldest byte
		tempStatus = SPIS_Ev_GetRxBufferSize();
        while (tempStatus) //get all availiable bytes
		{
			buffEv[tempBuffWrite] = SPIS_Ev_ReadRxData();
            tempBuffWrite = WRAPINC(tempBuffWrite, EV_BUFFER_SIZE);
            if (tempBuffWrite == buffEvRead) buffEvRead = WRAPINC(tempBuffWrite, EV_BUFFER_SIZE); //Discard oldest byte
            tempStatus = SPIS_Ev_GetRxBufferSize();
		}
		buffEvWrite = tempBuffWrite;
	}

	CyExitCriticalSection(intState);
}
//CY_ISR(ISRDrdyCap)
//{
//	uint8 intState = CyEnterCriticalSection();
//	uint8 tempStatus = Timer_Drdy_ReadStatusRegister();
//	
//	if ((0u != (tempStatus & Timer_Drdy_STATUS_CAPTURE)) && (0u != (tempStatus & Timer_Drdy_STATUS_FIFONEMP)))
//	{
//		uint8 tempCap;
//		while(0u != (Timer_Drdy_ReadStatusRegister() & Timer_Drdy_STATUS_FIFONEMP))
//		{
//			tempCap = Timer_Drdy_ReadCapture();
//			if (0u == Pin_nDrdy_Read())
//			{
//				lastDrdyCap = tempCap;
//			}
//		}
//	}
//	if (0u != (tempStatus & Timer_Drdy_STATUS_TC))
//	{
////		if ((0u != Pin_nDrdy_Read()) || (lastDrdyCap < MIN_DRDY_CYCLES))
////		{
//			timeoutDrdy = TRUE;
//			lastDrdyCap = Timer_Drdy_ReadPeriod();
////		}
////		else
////		{
////			Timer_Drdy_WriteCounter(Timer_Drdy_ReadPeriod());
////		if(0u != (Timer_Drdy_ReadControlRegister() & Timer_Drdy_CTRL_ENABLE ))
////		{
////			Timer_Drdy_Stop();
////		}
////			Timer_Drdy_Start();
////		}
//		
//	}
//	CyExitCriticalSection(intState);
//}

//CY_ISR(ISRHRTx)
//{
//
//	uint8 tempStatus;// = UART_HR_Data_ReadTxStatus();
////	uint8 intState = CyEnterCriticalSection();
////	UART_HR_Data_PutArray(buffSPIWrite, 34);
////	isr_HR_Disable();
////	if (UART_HR_Data_GetTxBufferSize() <= 1) for(uint8 x=0;x<34;x++) UART_HR_Data_PutChar(x);
////	tempStatus = UART_HR_Data_ReadTxStatus();
////	isr_HR_ClearPending();
////	isr_HR_Enable();
//	
////	if (0) //TODO integrate Baro and SPI to buffframedata
//	if (UART_HR_Data_GetTxBufferSize() <= 1)
//	{
////	if (FALSE !=((UART_HR_Data_TX_STS_FIFO_EMPTY | UART_HR_Data_TX_STS_COMPLETE) & tempStatus))
////	{
////		UART_HR_Data_PutArray((uint8 *)(&frameCnt), 3); //little endian, need big endian
//		
//		uint8 buffFrame[34];
//		uint8 ibuffFrame = 0;
//		
//		for (int i = 2; i >= 0; i--)
//		{
//			buffFrame[ibuffFrame] = *((uint8*)(((uint8*) &frameCnt) + i)); //this converts to big endian 3 byte counter
//			UART_HR_Data_PutChar(buffFrame[ibuffFrame]);
//			ibuffFrame++;
//		}
//		uint8 nullFrame = FALSE;
//		EvBufferIndex nDataBytesLeft = FRAME_DATA_BYTES;
////		memcpy( (buffFrame + ibuffFrame), &(frameCnt), 3);
////		ibuffFrame += 3;
//		frameCnt++;
//		memcpy( (buffFrame + ibuffFrame), frameSync, 2);
//		ibuffFrame += 2;
//		memcpy( (buffFrame + ibuffFrame), frameSync, 2);
//		ibuffFrame += 2;
////		buffUsbTxDebug[iBuffUsbTxDebug++] = '{';
////		buffUsbTxDebug[iBuffUsbTxDebug++] = packetFIFOHead;
////		buffUsbTxDebug[iBuffUsbTxDebug++] = '+';
////		buffUsbTxDebug[iBuffUsbTxDebug++] = packetFIFOTail;
////		buffUsbTxDebug[iBuffUsbTxDebug++] = '}';
////        if (FALSE) //DEBUG let event buffer fill
//        if (FRAME_DATA_BYTES <= WRAP(EV_BUFFER_SIZE - buffEvRead + buffEvWrite, EV_BUFFER_SIZE)) //Full frame of event data
//        {
//            EvBufferIndex nBytes;
//            EvBufferIndex curRead = buffEvRead;
//			EvBufferIndex curEOR = WRAP(curRead + (FRAME_DATA_BYTES - 1), EV_BUFFER_SIZE);
//			
//			if (curEOR > curRead)
//			{
//				nBytes = FRAME_DATA_BYTES;
//			}
//			else
//			{
//				nBytes = EV_BUFFER_SIZE - curRead;
//			}
//			memcpy( (buffFrame + ibuffFrame), buffEv + curRead, nBytes);
//			ibuffFrame += nBytes;
//			nDataBytesLeft -= nBytes;
////				curRead += (nBytes - 1); //avoiding overflow with - 1 , will add later
//
//			if (nDataBytesLeft > 0) //more data to fill frame
//			{
//                memcpy( (buffFrame + ibuffFrame), buffEv, nDataBytesLeft);
//			    ibuffFrame += nDataBytesLeft;
//			    nDataBytesLeft = 0;
//			}
//			curRead = WRAPINC(curEOR, EV_BUFFER_SIZE);
//            //TODO MUTEX or volatile
//            buffEvRead = curRead;
//        }
//		else if (packetFIFOHead == packetFIFOTail)
//		{
//			nullFrame = TRUE;
//		}
//		else
//		{
//			uint8 curSPIDev = packetFIFO[packetFIFOHead].index;
//			SPIBufferIndex nBytes;
//			SPIBufferIndex curEOR= packetFIFO[packetFIFOHead].EOR;
//			SPIBufferIndex curRead = buffSPIRead[curSPIDev];
////			buffUsbTxDebug[iBuffUsbTxDebug++] = '|';
////			buffUsbTxDebug[iBuffUsbTxDebug++] = curSPIDev;
////			buffUsbTxDebug[iBuffUsbTxDebug++] = '[';
////			buffUsbTxDebug[iBuffUsbTxDebug++] = curRead;
////			buffUsbTxDebug[iBuffUsbTxDebug++] = '-';
////			buffUsbTxDebug[iBuffUsbTxDebug++] = curEOR;
////			buffUsbTxDebug[iBuffUsbTxDebug++] = ']';
//			while((packetFIFOHead != packetFIFOTail) && (nDataBytesLeft > 0))
//			{
//				if (curEOR >= curRead)
//				{
//					nBytes = MIN(((curEOR - curRead) + 1), nDataBytesLeft);
//				}
//				else
//				{
//					nBytes = MIN(SPI_BUFFER_SIZE - curRead, nDataBytesLeft);
//				}
//				memcpy( (buffFrame + ibuffFrame), buffSPI[curSPIDev] + curRead, nBytes);
//				ibuffFrame += nBytes;
//				nDataBytesLeft -= nBytes;
////				curRead += (nBytes); //avoiding overflow with - 1 , will add later
//				curRead += (nBytes - 1); //avoiding overflow with - 1 , will add later
////				if ((curRead - 1)== curEOR)
//				if ((curRead)== curEOR)
//				{
//                    curRead = WRAPINC(curRead, SPI_BUFFER_SIZE); //last increment, handling the wrap
//					buffSPIRead[curSPIDev]= curRead % SPI_BUFFER_SIZE;
//					packetFIFOHead = WRAPINC(packetFIFOHead, PACKET_FIFO_SIZE);
//					if (packetFIFOHead != packetFIFOTail) 
//					{
//						curSPIDev = packetFIFO[packetFIFOHead].index;
//						curEOR = packetFIFO[packetFIFOHead].EOR;
//						curRead = buffSPIRead[curSPIDev];
//					}
//				}
////				else if (curRead >= (SPI_BUFFER_SIZE))
//				else if (curRead >= (SPI_BUFFER_SIZE - 1))
//				{
//					curRead = buffSPIRead[curSPIDev] = 0;
//				}
//				else
//				{
//                    curRead = WRAPINC(curRead, SPI_BUFFER_SIZE); //last increment, handling the wrap
//					buffSPIRead[curSPIDev] = curRead;
//				}
//			}
//		}
//		while (nDataBytesLeft > 0)
//		{
//			buffFrame[ibuffFrame] = NULL_HEAD;
////			UART_HR_Data_PutChar(NULL_HEAD);
//			ibuffFrame++;
//			nDataBytesLeft--;
//			if (nDataBytesLeft > 1)
//			{
//				memcpy( &(buffFrame[ibuffFrame]), frame00FF, 2);
//				ibuffFrame += 2;
//				nDataBytesLeft -= 2;
//			}
//			else //TODO this is an alignment error
//			{
//				if (1 == nDataBytesLeft)
//				{
//					buffFrame[ibuffFrame] = NULL_HEAD;
//					ibuffFrame++;
//					nDataBytesLeft--;
//				}
//                cntError++;
//			}
//		}
//		UART_HR_Data_PutArray((uint8 *)(buffFrame + 3), 31); //already sent the 3 byte counter, send rest of frame
//		if (TRUE != nullFrame)
//		{
//			memcpy((buffUsbTx + iBuffUsbTx), buffFrame, 34);
//			iBuffUsbTx += 34;
//		}
//	}
//	tempStatus = UART_HR_Data_ReadTxStatus();
//	if ((0u != USBUART_CD_GetConfiguration()) )//&& (iBuffUsbTx > 0))
//		{
// 
//			/* Wait until component is ready to send data to host. */
//			if (USBUART_CD_CDCIsReady()) // && ((iBuffUsbTx > 0) || (iBuffUsbTxDebug > 0)))
//			{
//				if (iBuffUsbTx > 0)
//				{
//					USBUART_CD_PutData(buffUsbTx, iBuffUsbTx);
//					iBuffUsbTx = 0; //TODO handle missed writes
//				}
//				if (iBuffUsbTxDebug > 0)
//				{
//					while (0 == USBUART_CD_CDCIsReady());
//					USBUART_CD_PutData(buffUsbTxDebug, iBuffUsbTxDebug);
//					iBuffUsbTxDebug = 0; //TODO handle missed writes
//				}
//			}
//		}
//		else
//		{
//			iBuffUsbTx = 0; //TODO handle missed writes
//			iBuffUsbTxDebug = 0; //TODO handle missed writes
//		}
//
////	CyExitCriticalSection(intState);
//}
CY_ISR(ISRBaroCap)
{
//	isr_B_ClearPending();
//    Pin_CE1_Write(1); //DEBUG
	uint8 continueCheck = FALSE;
//	uint8 n =0;
    //DEBUG
//    for(uint8 x =0; x<4; x++) buffBaroCapNum[x][buffBaroCapNumWrite] = 0;//DEBUG
	do {
		uint8 i = 0;
//		uint tempStatus = Counter_BaroTemp1_ReadStatusRegister();
//		UART_HR_Data_PutChar(Counter_BaroTemp1_STATUS_FIFONEMP);
//		UART_HR_Data_PutChar(tempStatus);
//		UART_HR_Data_PutChar(Counter_BaroTemp1_STATUS_FIFONEMP & tempStatus);
//		Counter_BaroTemp1_ReadCapture();
		continueCheck = FALSE;
		if (0 != (Counter_BaroTemp1_STATUS_FIFONEMP & Counter_BaroTemp1_ReadStatusRegister()))
		{
			continueCheck = TRUE;
			buffBaroCap[i][buffBaroCapWrite[i]] = Counter_BaroTemp1_ReadCapture();
			buffBaroCapWrite[i] = WRAPINC(buffBaroCapWrite[i], NUM_BARO_CAPTURES);
//            buffBaroCapNum[i][buffBaroCapNumWrite]++; //DEBUG
		}
		i = 2;
		if (0 != (Counter_BaroTemp2_STATUS_FIFONEMP & Counter_BaroTemp2_ReadStatusRegister()))
		{
			continueCheck = TRUE;
			buffBaroCap[i][buffBaroCapWrite[i]] = Counter_BaroTemp2_ReadCapture();
			buffBaroCapWrite[i] = WRAPINC(buffBaroCapWrite[i], NUM_BARO_CAPTURES);
//            buffBaroCapNum[i][buffBaroCapNumWrite]++;//DEBUG
		}
		i = 1;
		if (0 != (Counter_BaroPres1_STATUS_FIFONEMP & Counter_BaroPres1_ReadStatusRegister()))
		{
			continueCheck = TRUE;
			buffBaroCap[i][buffBaroCapWrite[i]] = Counter_BaroPres1_ReadCapture();
			buffBaroCapWrite[i] = WRAPINC(buffBaroCapWrite[i], NUM_BARO_CAPTURES);
//            buffBaroCapNum[i][buffBaroCapNumWrite]++; //DEBUG
		}
		i = 3;
		if (0 != (Counter_BaroPres2_STATUS_FIFONEMP & Counter_BaroPres2_ReadStatusRegister()))
		{
			continueCheck = TRUE;
			buffBaroCap[i][buffBaroCapWrite[i]] = Counter_BaroPres2_ReadCapture();
			buffBaroCapWrite[i] = WRAPINC(buffBaroCapWrite[i], NUM_BARO_CAPTURES);
//            buffBaroCapNum[i][buffBaroCapNumWrite]++; //DEBUG
		}
//		n++;
	} while(continueCheck);
//    if (buffBaroCapNumWrite >= (NUM_BARO_CAPTURES - 1))//DEBUG
//    {
//        buffBaroCapNumWrite = 0 ;
//    }
//    else
//    {
//        buffBaroCapNumWrite++;//DEBUG
//	}
    //TODO Packing of Baro values along with thers like voltage.  For now just dump it to stream
//	UART_HR_Data_PutChar(DUMP_HEAD);
//	UART_HR_Data_PutChar(n);
//	UART_HR_Data_PutArray((uint8*) buffBaroCap, sizeof(buffBaroCap));
//	UART_HR_Data_PutChar(ENDDUMP_HEAD);
//	for (uint8 i=0;i<(NUM_BARO *2); i++) buffBaroCapRead[i] = buffBaroCapWrite[i];
    for (uint8 i=0;i<(NUM_BARO); i++) 
    {
        uint8 n = i << 1;
        uint16 temp16;
//        uint16 last16 =(uint16)(curBaroTempCnt[i] & 0xFFFF);
        uint16 last16 = buffBaroCap[n][WRAPDEC( buffBaroCapRead[n] , NUM_BARO_CAPTURES)];
//        uint8 numRollover = 0;
        while(buffBaroCapRead[n] != buffBaroCapWrite[n])
        {
            temp16 = buffBaroCap[n][buffBaroCapRead[n]];
            if ( last16 > temp16)
            {
//                curBaroTempCnt[i] += 0x10000; // rollover, increment upper MSB
//                numRollover++;
                curBaroTempCnt[i] += (uint32)(BARO_COUNT_MAX - last16); //add the rest of counter before rollover
                curBaroTempCnt[i] += (uint32)(temp16); //add counter after rollover
            }
            else
            {
                curBaroTempCnt[i] += (uint32)(temp16 - last16); //add counter after rollover
            }
            buffBaroCapRead[n] = WRAPINC( buffBaroCapRead[n] , NUM_BARO_CAPTURES);
            last16 = temp16;
//            if (buffBaroCapRead[n] == buffBaroCapWrite[n])
//            {
//                curBaroTempCnt[i] &= 0xFFFF0000;
//                curBaroTempCnt[i] |= temp16;
//            }
//            else
//            {
//                last16 = temp16;
//            }
        }
//        for (uint8 x=0;x<numRollover; x++) curBaroTempCnt[i] += 0xFFFE; // period of the 16 bit counter maxes out at 65534 so add that per rollover, counter immediately turns to 0 at that count and counts up to 1 next baro pulse
        n++;
        last16 = buffBaroCap[n][WRAPDEC( buffBaroCapRead[n] , NUM_BARO_CAPTURES)];
//        last16 =(uint16)(curBaroPresCnt[i] & 0xFFFF);
//        numRollover = 0;
        while(buffBaroCapRead[n] != buffBaroCapWrite[n])
        {
            temp16 = buffBaroCap[n][buffBaroCapRead[n]];
            if ( last16 > temp16)
            {
//                curBaroPresCnt[i] += 0x10000; // rollover, increment upper MSB
//                numRollover++;
                curBaroPresCnt[i] += (uint32)(BARO_COUNT_MAX - last16); //add the rest of counter before rollover
                curBaroPresCnt[i] += (uint32)(temp16); //add counter after rollover
            }
            else
            {
                curBaroPresCnt[i] += (uint32)(temp16 - last16); //add counter after rollover
            }
            buffBaroCapRead[n] = WRAPINC( buffBaroCapRead[n] , NUM_BARO_CAPTURES);
            last16 = temp16;
//            if (buffBaroCapRead[n] == buffBaroCapWrite[n])
//            {
//                curBaroPresCnt[i] &= 0xFFFF0000;
//                curBaroPresCnt[i] |= temp16;
//            }
//            else
//            {
//                last16 = temp16;
//            }
        }
//        for (uint8 x=0;x<numRollover; x++) curBaroPresCnt[i] += 0xFFFE; // period of the 16 bit counter maxes out at 65534 so add that per rollover, counter immediately turns to 0 at that count and counts up to 1 next baro pulse
    }
//	uint8 tmpSecs =  hkSecs << 1; //ISR is now 2Hz so need to adjust hkSecs to match
	uint8 tmpSecs =  hkSecs << 2; //ISR is now 4Hz so need to adjust hkSecs to match
//	Pin_CE1_Write(cntSecs % 2); //DEBUG timing on scope
    if (0 == (cntSecs % tmpSecs))
    {
        RTC_Main_DisableInt();
        mainTimeDateSysPtr = RTC_Main_ReadTime();
        memcpy(&mainTimeDate, mainTimeDateSysPtr, sizeof(mainTimeDate));// copy to local struct before update
        RTC_Main_EnableInt();
        hkReq = TRUE;//request a new housekeeping packet
        if ((255 - cntSecs) <= tmpSecs)
        {
            cntSecs=1;// reset to 1 before the rollover to 0 causes incosistant interval timing
        }
        else
        {
            cntSecs++;
        }
        uint32 temp32 = curBaroTempCnt[0];
//        int8 i=2; //24bit for Counter1 style packet DEBUG
        int8 i=3; //32bit 
        buffHK[buffHKWrite].baroTemp1[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
        while (0 <= --i) //Fill the Higher order bytes
        {
            temp32 >>= 8;
            buffHK[buffHKWrite].baroTemp1[i] = temp32 & 0xFF;
        }
        temp32 = curBaroPresCnt[0];
        i=3; //32bit
//        i=2; //24bit for Counter1 style packet DEBUG
        buffHK[buffHKWrite].baroPres1[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
        while (0 <= --i) //Fill the Higher order bytes
        {
            temp32 >>= 8;
            buffHK[buffHKWrite].baroPres1[i] = temp32 & 0xFF;
        }
        temp32 = curBaroTempCnt[1];
        i=3; //32bit
//        i=2; //24bit for Counter1 style packet DEBUG
        buffHK[buffHKWrite].baroTemp2[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
        while (0 <= --i) //Fill the Higher order bytes
        {
            temp32 >>= 8;
            buffHK[buffHKWrite].baroTemp2[i] = temp32 & 0xFF;
        }
        temp32 = curBaroPresCnt[1];
        i=3; //32bit
//        i=2; //24bit for Counter1 style packet DEBUG
        buffHK[buffHKWrite].baroPres2[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
        while (0 <= --i) //Fill the Higher order bytes
        {
            temp32 >>= 8;
            buffHK[buffHKWrite].baroPres2[i] = temp32 & 0xFF;
        }
        
        temp32 = (uint32)(mainTimeDate.Year % 2000) << 4;
        temp32 |= mainTimeDate.Month;
        temp32 <<= 5;//shift left to make room for new bits;
        temp32 |= mainTimeDate.DayOfMonth;
        temp32 <<= 5;//shift left to make room for new bits;
        temp32 |= mainTimeDate.Hour;
        temp32 <<= 6;//shift left to make room for new bits;
        temp32 |= mainTimeDate.Min;
        temp32 <<= 6;//shift left to make room for new bits;
        temp32 |= mainTimeDate.Sec;
        
//        temp32 = 60 * ( ( 60 * mainTimeDate.Hour) + mainTimeDate.Min ) + mainTimeDate.Sec; // Convert RTC to secs
        i=3; //32bit
//        i=2; //24bit for Counter1 style packet DEBUG
        buffHK[buffHKWrite].packedTimeDate[i] = temp32 & 0xFF; // to make this endian independent and output as big endian, fill the LSB first
        while (0 <= --i) //Fill the Higher order bytes
        {
            temp32 >>= 8;
            buffHK[buffHKWrite].packedTimeDate[i] = temp32 & 0xFF;
        }

    }
    else
    {
        cntSecs++;
    }
//    Pin_CE1_Write(0); //DEBUG
    
}



int main(void)
{
//	uint8 status;
//	uint8 fillByte = 0xA3u;
//	cmdBuff[CMDBUFFSIZE - 1] = FILLBYTE;
//	uint8 buffUsbTx[SPI_BUFFER_SIZE];
//	uint8 iBuffUsbTx = 0;
//	uint8 buffUsbTxDebug[SPI_BUFFER_SIZE];
//	uint8 iBuffUsbTxDebug = 0;
	uint8 buffUsbRx[USBUART_BUFFER_SIZE];
	uint8 iBuffUsbRx = 0;
	uint8 nBuffUsbRx = 0;
	enum readStatus readStatusBP = CHECKDATA;
    /* Variable declarations for DMA_LR_Cmd_1 */
    /* Move these variable declarations to the top of the function */
//    uint8 DMA_LR_Cmd_1_Chan;
//    uint8 DMA_LR_Cmd_1_TD[1];
    buffEvRead = buffEvWrite = 0;
	memset(buffSPIRead, 0, NUM_SPI_DEV);
	memset(buffSPIWrite, 0, NUM_SPI_DEV);
	memset(buffSPICurHead, 0, NUM_SPI_DEV);
	memset(buffSPICompleteHead, 0, NUM_SPI_DEV);
	memset(buffUsbTx, 0, USBUART_BUFFER_SIZE);
//	memset(curBaroTemp, 0, (sizeof(double) * NUM_BARO));
//	memset(curBaroPres, 0, (sizeof(double) *  NUM_BARO));
	memset(curBaroTempCnt, 0, (sizeof(uint32) * NUM_BARO));
	memset(curBaroPresCnt, 0, (sizeof(uint32) * NUM_BARO));
	memset(buffBaroCap, 0, (sizeof(uint16) * (NUM_BARO * NUM_BARO_CAPTURES)));
	memset(buffBaroCapRead, 0, NUM_BARO);
	memset(buffBaroCapWrite, 0, NUM_BARO);
    memset(commandStatusC, WAIT_DLE, COMMAND_SOURCES);
//    memset(buffCmdRxCRead, 0, COMMAND_SOURCES);
    memset(readBuffCmd, 0, COMMAND_SOURCES);
    memset(writeBuffCmd, 0, COMMAND_SOURCES);
    
    for (uint8 i = 0; i < COMMAND_SOURCES; i++)
    {
        orderBuffCmd[i] = i; //read the cmd buff in order
    }
//    memcpy(&buffCmd[0][0][0], initCmd, (NUMBER_INIT_CMDS * 2));
//    writeBuffCmd[0] = NUMBER_INIT_CMDS;
//    memcpy(&buffCmd[1][0][0], initCmd, (NUMBER_INIT_CMDS * 2));
//    writeBuffCmd[1] = NUMBER_INIT_CMDS;
    
//	buffUsbTx[3] = 0x55;
//	buffUsbTx[4] = 0xAA;
//	buffUsbTx[5] = 0x55;
//	buffUsbTx[6] = 0xAA;
//	iBuffUsbTx = 7;
//	uint16 tempSpinTimer = 0; //TODO replace
	
    /* DMA Configuration for DMA_LR_Cmd_1 */
//    DMA_LR_Cmd_1_Chan = DMA_LR_Cmd_1_DmaInitialize(DMA_LR_Cmd_1_BYTES_PER_BURST, DMA_LR_Cmd_1_REQUEST_PER_BURST, 
//        HI16(DMA_LR_Cmd_1_SRC_BASE), HI16(DMA_LR_Cmd_1_DST_BASE));
//    DMA_LR_Cmd_1_TD[0] = CyDmaTdAllocate();
//    CyDmaTdSetConfiguration(DMA_LR_Cmd_1_TD[0], DMA_LR_Cmd_1_BUFFER_SIZE, DMA_LR_Cmd_1_TD[0], CY_DMA_TD_INC_DST_ADR);
//    CyDmaTdSetAddress(DMA_LR_Cmd_1_TD[0], LO16((uint32)UART_LR_Cmd_1_RXDATA_REG), LO16((uint32)buffCmdRxC[0]));
//    CyDmaChSetInitialTd(DMA_LR_Cmd_1_Chan, DMA_LR_Cmd_1_TD[0]);
//    CyDmaChEnable(DMA_LR_Cmd_1_Chan, 1);
    
//    buffCmdRxCWritePtr[0] = (reg16 *) &CY_DMA_TDMEM_STRUCT_PTR[0].TD1[2u];
    I2C_RTC_Start();
    
	SPIM_BP_Start();
	SPIM_BP_ClearFIFO();
    SPIS_Ev_Start();
//	USBUART_CD_Start(USBFS_DEVICE, USBUART_CD_5V_OPERATION);
	USBUART_CD_Start(USBFS_DEVICE, USBUART_CD_3V_OPERATION);
	UART_Cmd_Start();
	UART_HR_Data_Start();
	UART_LR_Cmd_1_Start();
	UART_LR_Cmd_2_Start();
	UART_LR_Data_Start();
	Timer_SelLow_Stop();
    
    Pin_Sel2_Pwr_Write(0);
    Pin_Sel5_HV1_Write(0);
    Pin_Sel6_HV2_Write(0);
   
    Pin_Sel3_J16_Write(0);
    Pin_Sel12_J17_Write(0);
    Pin_Sel13_J18_Write(0);
    Pin_Sel7_J20_Write(0);
    
    Pin_Reset_Ev_SW_Write(0);
    Pin_Reset_Ev_HW_Write(1); //Configed as hardware reset, so should be kept high during run
    
		   /* Service USB CDC when device is configured. */
//	if ((0u != USBUART_CD_GetConfiguration()) && (iBuffUsbTx > 0))
//	{
//
//		/* Wait until component is ready to send data to host. */
//		if (USBUART_CD_CDCIsReady())
//		{
//			USBUART_CD_PutChar('S'); //TODO  different or eliminate startup message
//		}
//	}
//	lastDrdyCap = Timer_Drdy_ReadPeriod();
	
	Control_Reg_R_Write(0x00u); //set global reset off to start boards and components
	Control_Reg_MIP_Out_Write(0x03u); //Output Data packet to both MIP

//	Control_Reg_SS_Write(tabSPISel[0u]);
//	Control_Reg_CD_Write(1u);
	
    Pin_Busy_Write(outputBusy);//signal not busy by default
    
	isr_R_StartEx(ISRReadSPI);
	isr_W_StartEx(ISRWriteSPI);
//	isr_C_StartEx(ISRDrdyCap);
	isr_E_StartEx(ISRReadEv);
	isr_Cm_StartEx(ISRCheckCmd);//RTC startup reads mostly 0s out when this is moved after tha sequence 
    isr_Cm_Disable();//Init commands are not enqueued so no interrupts for more commands
	
	
//	Timer_Tsync_Start();
//	Timer_SelLow_Start();
//	Timer_Drdy_Start();

	Counter_BaroPres1_Start();
	Counter_BaroTemp1_Start();
	Counter_BaroPres2_Start();
	Counter_BaroTemp2_Start();
//	cmdBuff[0] = 0x0Fu;
//	cmdBuff[1] = 0xF0u;
//	SPIM_BP_WriteTxData(cmdBuff[0]);
//	iCmdBuff = 1;
	SPIM_BP_TxDisable();
//	for(uint8 x=0;x<34;x++) UART_HR_Data_PutChar(x);
	CyGlobalIntEnable; /* Enable global interrupts. */
//	ISRHRTx();
//	isr_HR_StartEx(ISRHRTx);
	
//	SendInitCmds();
	isr_B_StartEx(ISRBaroCap);
    
    InitRTC();
    //Debug 1 write and read
//    buffI2CRead = 0;
//    buffI2CWrite = 2;
//    uint8 registerToRead = 0x01;
//    uint8 tmpI2Cdata[8];
//    memset(tmpI2Cdata, 0, 8);
//    buffI2C[buffI2CRead].type = I2C_WRITE;
//    buffI2C[buffI2CRead].slaveAddress = I2C_Address_INA226_5V_Dig;
//    buffI2C[buffI2CRead].data = &registerToRead;
//    buffI2C[buffI2CRead].cnt = 1;
//    buffI2C[buffI2CRead].mode = I2C_RTC_MODE_COMPLETE_XFER;
//    buffI2C[buffI2CRead + 1].type = I2C_READ;
//    buffI2C[buffI2CRead + 1].slaveAddress = I2C_Address_INA226_5V_Dig;
//    buffI2C[buffI2CRead + 1].data = tmpI2Cdata;
//    buffI2C[buffI2CRead + 1].cnt = 8;
//    buffI2C[buffI2CRead + 1].mode = I2C_RTC_MODE_COMPLETE_XFER;
    
    InitFrameBuffer(); //intialize sync and seq num
    InitHKBuffer();
    InitLRScienceData();
    DMAHRDataChan  = DMA_HR_Data_DmaInitialize(DMA_HR_Data_BYTES_PER_BURST, DMA_HR_Data_REQUEST_PER_BURST, HI16(DMA_HR_Data_SRC_BASE), HI16(DMA_HR_Data_DST_BASE)); //keep this high rate channel for UART
    
//    CyDelay(7000); //7 sec delay for boards to init TODO Debug

    I2C_RTC_MasterClearStatus();
    rtcStatus = RTS_SET_MAIN; //changing flags in this will change startup behavior of RTCs
    CyDelay(1000); //sec delay for boards to init TODO Debug
    
    do  //get set RTC Main
    {
        CheckRTC();//needed to process RTC
        CheckI2C();//needed to process RTC
    }while(0 != rtcStatus) ;//Main RTC Set TODO Timeout
    rtcStatus = RTS_SET_EVENT; //changing flags in this will change startup behavior of RTCs
//    CyDelay(500); //half sec delay for boards to init TODO Debug
    
    do  //get set RTC Event
    {
        CheckRTC();//needed to process RTC
        CheckCmdBuffers();//needed to process RTC
    }while(0 != rtcStatus) ;//Event RTC commands issued TODO Timeout
    
    while(readBuffCmd[0] != writeBuffCmd[0]) //Finish all commands TODO Timeout
    {
        CheckCmdBuffers();//needed to process RTC
    };
    SendInitCmds();//Enqueued all init commands
	isr_Cm_Enable();//Since init commands are enqueued, start interrupts for more commands
    InitBaroI2COTP();//start the process of getting these OTP coefficients once
	for(;;)
	{
		
		/* Place your application code here. */
        int tempRes = CheckCmdBuffers();
        tempRes = CheckEventPackets(); //TODO Move order of this call
        tempRes = CheckFrameBuffer(); //TODO Move order of this call
        tempRes = CheckHKBuffer(); //TODO Move order of this call
        tempRes = CheckLRScienceData(); //TODO Move order of this call
        
        
		//if (SPIM_BP_GetRxBufferSize > 0)
		//{
//			SPIM_BP_ReadRxData();
			

		//while(Pin_Sel_Read());
		
			
//			do{
//				status = SPIM_BP_ReadTxStatus();
//			}while (!(status & ( SPIM_BP_STS_SPI_IDLE)));
			
//			while((Status_Reg_nSS_Read()));
//			SPIM_BP_ClearTxBuffer();
//
//			SPIM_BP_WriteTxData(fillByte);
		//}
		if (0u != USBUART_CD_IsConfigurationChanged())
		{
			/* Initialize IN endpoints when device is configured. */
			if (0u != USBUART_CD_GetConfiguration())
			{
				/* Enumeration is done, enable OUT endpoint to receive data 
				 * from host. */
				USBUART_CD_CDC_Init();
			}
		}

		/* Service USB CDC when device is configured. */
		if ((nBuffUsbRx == iBuffUsbRx) && (0u != USBUART_CD_GetConfiguration()))
		{
			/* Check for input data from host. */
			if (0u != USBUART_CD_DataIsReady())
			{
				/* Read received data and re-enable OUT endpoint. */
				nBuffUsbRx = USBUART_CD_GetAll(buffUsbRx);
				iBuffUsbRx = 0;
//                buffUsbTxDebug[iBuffUsbTxDebug++] = nBuffUsbRx; //Debug

			}
		}
//		if ((6 == nBuffUsbRx) && (DLE == buffUsbRx[0])) //debug 
//		{
//            UART_LR_Data_PutArray(buffUsbRx, 6);
////            buffUsbTxDebug[iBuffUsbTxDebug++] = '^'; //Debug
////            buffUsbTxDebug[iBuffUsbTxDebug++] = CY_DMA_TDMEM_STRUCT_PTR[0].TD1[2u] & 15; //Debug
//            
////            memcpy(buffUsbTxDebug + iBuffUsbTxDebug, buffCmdRxC, 16);
////            iBuffUsbTxDebug +=16; //debug
//        }
//        else //debug
//        {
//            UART_LR_Data_PutArray(buffUsbRx, nBuffUsbRx);
//        }
        
        for(uint8 x = 0; x < nBuffUsbRx; x++)
        {
            tempRes = ParseCmdInputByte(buffUsbRx[x], (COMMAND_SOURCES - 1));
            if (0 > tempRes)
            {
                //TODO error handling
            }
        }
        iBuffUsbRx = 0;
        nBuffUsbRx = 0;
//		if (nBuffUsbRx > iBuffUsbRx)
//		{
//			uint8 nByteCpy =  MIN(COMMAND_CHARS - iCurCmd, nBuffUsbRx - iBuffUsbRx);
//			if (nByteCpy > 0)
//			{
//				memcpy((curCmd + iCurCmd), (buffUsbRx + iBuffUsbRx), nByteCpy);
//				iCurCmd += nByteCpy;
//				iBuffUsbRx += nByteCpy;
//			}
//				
//			if ((iCurCmd >= COMMAND_CHARS) && (0u != (UART_Cmd_TX_STS_FIFO_EMPTY | UART_Cmd_ReadTxStatus())))
//			{
//				uint8 cmdValid = TRUE;
//				//all nibbles of the command must be uppercase hex char 
//				for(uint8 x = 0; ((x < COMMAND_CHARS) && cmdValid); x++)
//				{
//					if ((!(isxdigit(curCmd[x]))) || (curCmd[x] > 'F'))
//					{
//						cmdValid = FALSE; 
//					}
//				}
//				if (cmdValid)
//				{
//					//DEBUG echo command no boundary check
//					memcpy(buffUsbTxDebug, "++", 2);
//					memcpy(buffUsbTxDebug +2, curCmd, COMMAND_CHARS);
//					iBuffUsbTxDebug += 6;
//					//Write 3 times cmd on backplane
//                    SendCmdString(curCmd);//, FALSE);
////					for (uint8 x=0; x<3; x++)
////					{
////						UART_Cmd_PutArray(START_COMMAND, START_COMMAND_SIZE);
////						memcpy(buffUsbTxDebug + iBuffUsbTxDebug, START_COMMAND, START_COMMAND_SIZE);
////						iBuffUsbTxDebug += START_COMMAND_SIZE;
////						UART_Cmd_PutArray(curCmd, COMMAND_CHARS);
////						memcpy(buffUsbTxDebug + iBuffUsbTxDebug, curCmd, COMMAND_CHARS);
////						iBuffUsbTxDebug += COMMAND_CHARS;
////						UART_Cmd_PutArray(END_COMMAND, END_COMMAND_SIZE);
////						memcpy(buffUsbTxDebug + iBuffUsbTxDebug, END_COMMAND, END_COMMAND_SIZE);
////						iBuffUsbTxDebug += END_COMMAND_SIZE;
////					}
////					//Unix style line end
////					UART_Cmd_PutChar(CR);
////					UART_Cmd_PutChar(LF);	
//				}
//				else 
//				{
//					//DEBUG echo command no boundary check
//					memcpy(buffUsbTxDebug, "--", 2);
//					memcpy(buffUsbTxDebug + 2, curCmd, COMMAND_CHARS);
//					iBuffUsbTxDebug += 6;
//				}
//				iCurCmd = 0;	
//			}
			
//		}
//		CheckCmdDma(0);
        
		switch (readStatusBP)
		{
            uint8 tempnDrdy;
			case CHECKDATA:
                
				Timer_SelLow_Stop();
                
//				if(0u == (Timer_Drdy_ReadControlRegister() & Timer_Drdy_CTRL_ENABLE ))
//				{
//				Control_Reg_CD_Write(0x01u);
                
                
//					lastDrdyCap = Timer_Drdy_ReadPeriod();
//					Timer_Drdy_Start();
					
//				}
//                (*tabSPISel[iSPIDev])(1u);//select high to check the selected board
                tempnDrdy = Pin_nDrdy_Filter_Read();
                uint8 highLoops;
                if (loopCount < loopCountCheck) // check overflow
                {
                    highLoops = (255 - loopCountCheck) + loopCount;
                }
                else
                {
                    highLoops = loopCount - loopCountCheck;
                }
//                uint8 tempnDrdy = Pin_nDrdy_Filter_Read();
//                if(FALSE) //TODO New gltch filter test
//				if (TRUE == timeoutDrdy)
                
                
                if (SELECT_HIGH_LOOPS < highLoops) //timeout, no data
				{  
//					if (iSPIDev >= (NUM_SPI_DEV - 1))
//					{
//						iSPIDev = 0;
//					}
//					else
//					{
//						iSPIDev++;
//					}
//					if (0x0FFFu == ++tempSpinTimer)
//					{
//					Control_Reg_CD_Write(0u);
                    (*tabSPISel[iSPIDev])(0u);//select low before switching
					iSPIDev = WRAPINC(iSPIDev, NUM_SPI_DEV);
                    (*tabSPISel[iSPIDev])(0u);//select low before and wait for high
//                    (*tabSPISel[iSPIDev])(1u);//select high to check the selected board
//					Control_Reg_SS_Write(tabSPISel[iSPIDev]);
//					Control_Reg_CD_Write(1u);
					
//					timeoutDrdy = FALSE;
//					lastDrdyCap = Timer_Drdy_ReadPeriod();
//					Timer_Drdy_Stop();
//					Timer_Drdy_Start();
//					tempSpinTimer = 0;
//					}
                    loopCountCheck = loopCount;
				}
                else if ((SELECT_HIGH_LOOPS / 4) < highLoops) //time to sel high 
                {
                    (*tabSPISel[iSPIDev])(1u);//select high to check the selected board
                    if (0u == tempnDrdy) 
    				{
    //					uint8 tempLastDrdyCap = lastDrdyCap;
    //					Timer_Drdy_SoftwareCapture();
    //					uint8 tempCounter = Timer_Drdy_ReadCounter();
    //					if (tempCounter > tempLastDrdyCap) tempCounter = 0;
    					//if ((0u == Pin_nDrdy_Read()) && (0u != (SPIM_BP_TX_STATUS_REG & SPIM_BP_STS_TX_FIFO_EMPTY)))
    //                    if(FALSE) //TODO New gltch filter test
    //					if ((tempLastDrdyCap - tempCounter) >= MIN_DRDY_CYCLES)
    //					{
    						SPIBufferIndex tempBuffWrite = buffSPIWrite[iSPIDev];
    //						Control_Reg_CD_Write(0x03u);
    						Control_Reg_LoadPulse_Write(0x01u);
    						buffSPICurHead[iSPIDev] = buffSPIWrite[iSPIDev];
    						buffSPIWrite[iSPIDev] = WRAP3INC(tempBuffWrite, SPI_BUFFER_SIZE);
    						if (0u != (SPIM_BP_STS_TX_FIFO_EMPTY | SPIM_BP_TX_STATUS_REG))
    						{
    							SPIM_BP_WriteTxData(FILLBYTE);
    						}
    						
    						buffSPI[iSPIDev][tempBuffWrite] = tabSPIHead[iSPIDev];
    						tempBuffWrite=WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
    						if((SPI_BUFFER_SIZE - 1) == tempBuffWrite) //check for 2 byte wrap
    						{
    							buffSPI[iSPIDev][(SPI_BUFFER_SIZE - 1)] = frame00FF[0];
    							buffSPI[iSPIDev][0] = frame00FF[1];
    						}
    						else
    						{
    							memcpy(&(buffSPI[iSPIDev][tempBuffWrite]), frame00FF, 2);
    						}
    						
    	  
    						
    						continueRead = TRUE; 
    						readStatusBP = READOUTDATA;
    //						timeoutDrdy = FALSE;
    //						lastDrdyCap = Timer_Drdy_ReadPeriod();
    						
    //						if(0u != (Timer_Drdy_ReadControlRegister() & Timer_Drdy_CTRL_ENABLE ))
    //						{   
    //							Timer_Drdy_Stop();
    //						}
    //						tempSpinTimer = 0;
    //					}
    //					else //TODO New gltch filter test
    //					{
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = '=';
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = tempLastDrdyCap;
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = '-';
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = tempCounter;
    //						lastDrdyCap = tempLastDrdyCap;
    //					}
				    }
                }
                else
                {
                    (*tabSPISel[iSPIDev])(0u);//select low, wait for high
    				continueRead = FALSE; 
                }
//                else if(FALSE) //TODO New gltch filter test
//				else if ((0u == Pin_nDrdy_Read()) )//&& (0u == (Timer_Drdy_ReadStatusRegister() & Timer_Drdy_STATUS_FIFONEMP)))
                
				
				break;
				
			case READOUTDATA:
				//TODO actually check 3 byte EOR, count errrors 
//				Control_Reg_CD_Write(0u);
//				if (TRUE == continueRead)
//				{
//					//if (continueReadFlags == (continueReadFlags | SPIM_BP_TX_STATUS_REG))
//					if ((0u != (SPIM_BP_STS_SPI_IDLE | SPIM_BP_TX_STATUS_REG)))
//					{
//						if (0u != (SPIM_BP_STS_TX_FIFO_EMPTY | SPIM_BP_TX_STATUS_REG))
//						{
//							if (0x0005 == ++tempSpinTimer)
//							{
//								SPIM_BP_WriteTxData(FILLBYTE);
//								tempSpinTimer = 0;
//							}
//							
//						}
//					}
//				}
//				if (0u == (0x03u & Control_Reg_CD_Read()))
//                if((FALSE == continueRead) && (0u == (Timer_SelLow_ReadControlRegister() & Timer_SelLow_CTRL_ENABLE )))
                if((FALSE == continueRead) && (0u == (Timer_SelLow_CONTROL & Timer_SelLow_CTRL_ENABLE )))
				{
//                    Control_Reg_CD_Write(0u);
					if (buffSPICurHead[iSPIDev] == buffSPIWrite[iSPIDev]) //TODO this should't be true due to ISR
					{
											
//						uint8 nBytes = SPI_BUFFER_SIZE - buffSPIRead[iSPIDev];
//						
//						
//						memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][buffSPIRead[iSPIDev]]), nBytes);
//						iBuffUsbTx += nBytes;
//						if (nBytes < SPI_BUFFER_SIZE)
//						{
//							nBytes = SPI_BUFFER_SIZE - nBytes;
//							memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][0]), nBytes);
//							iBuffUsbTx += nBytes;
//						}
						readStatusBP = EORERROR;
					}
					//if ((1u == Pin_nDrdy_Read()) && (0u != (SPIM_BP_STS_SPI_IDLE | SPIM_BP_TX_STATUS_REG)))
					else
					{
						SPIBufferIndex tempBuffWrite = buffSPIWrite[iSPIDev];
						int16 tempLen = tempBuffWrite - buffSPICurHead[iSPIDev];
                        
//						uint8 nBytes;
						
                        if (0 > tempLen) tempLen += SPI_BUFFER_SIZE;
                        
                        tempLen %= 3; //bytes over 3 byte alignment
                        
                        if (tempLen) tempLen = 3 - tempLen; //check if not 3 byte aligned, then calculate number of padding bytes
                        
                        int16 tempLeft = buffSPIRead[iSPIDev] - tempBuffWrite;
                        if (0 > tempLeft) tempLeft += SPI_BUFFER_SIZE;
                        
                        if (tempLeft < (tempLen + 3))
                        {
                            readStatusBP = EORERROR;
                        }
                        else 
                        {
                            if (tempLen)
                            {
                                while (tempLen--)
                                {
                                    buffSPI[iSPIDev][tempBuffWrite] = 0; //pad 0
                                    tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
                                }
                                //buffSPIWrite[iSPIDev] = tempBuffWrite;
//                                tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
                            }
    						buffSPIWrite[iSPIDev] = WRAP3INC(tempBuffWrite, SPI_BUFFER_SIZE);
    						buffSPI[iSPIDev][tempBuffWrite] = EOR_HEAD;
    						tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
    						if((SPI_BUFFER_SIZE - 1) == tempBuffWrite) //check for 2 byte wrap
    						{
    							buffSPI[iSPIDev][(SPI_BUFFER_SIZE - 1)] = frame00FF[0];
    							buffSPI[iSPIDev][0] = frame00FF[1];
//    							tempBuffWrite = 1;
    						}
    						else
    						{
    							memcpy(&(buffSPI[iSPIDev][tempBuffWrite]), frame00FF, 2); //Copy 0x00FF
//    							tempBuffWrite += 1; 
//                                tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE); //this is te locatiion of the last byte
    						}
    						
    						packetFIFO[packetFIFOTail].header = buffSPICompleteHead[iSPIDev] = buffSPICurHead[iSPIDev];
    						packetFIFO[packetFIFOTail].index = iSPIDev;
                            if (buffSPIWrite[iSPIDev])
                            {
    						    packetFIFO[packetFIFOTail].EOR = buffSPIWrite[iSPIDev] - 1;
                            }
                            else
                            {
    						    packetFIFO[packetFIFOTail].EOR = SPI_BUFFER_SIZE - 1;
                            }
    						packetFIFOTail = WRAPINC(packetFIFOTail, PACKET_FIFO_SIZE);
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = '|';
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = iSPIDev;
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = '[';
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = buffSPICurHead[iSPIDev];
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = '-';
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = tempBuffWrite;
    //						buffUsbTxDebug[iBuffUsbTxDebug++] = ']';
    						
    						
    						
    //						buffSPI[iSPIDev][tempBuffWrite] = 0x00;
    //						tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
    //						buffSPI[iSPIDev][tempBuffWrite] = 0xFF;
    //						tempBuffWrite = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
    //						if (buffSPIRead[iSPIDev] >= tempBuffWrite)
    //						{
    //							nBytes = SPI_BUFFER_SIZE - buffSPIRead[iSPIDev];
    //							memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][buffSPIRead[iSPIDev]]), nBytes);
    //							iBuffUsbTx += nBytes;
    //							buffSPIRead[iSPIDev] = 0;
    //						}
    //						nBytes = tempBuffWrite - buffSPIRead[iSPIDev];
    //						memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][buffSPIRead[iSPIDev]]), nBytes);
    //						iBuffUsbTx += nBytes;
    //						buffSPIRead[iSPIDev] = tempBuffWrite;
    						readStatusBP = EORFOUND;
                        }
					}
					 
				}
                //TODO timeout
//				else 
//				{
//					if (0u != (SPIM_BP_STS_SPI_IDLE | SPIM_BP_TX_STATUS_REG))
//					{
//						if (0x0FFFu == ++tempSpinTimer)
//						{
//							readStatusBP = EORERROR;
//						}
//					}
//					else
//					{
//						tempSpinTimer = 0;
//					}
//				}
				break;
				
			case EORERROR:
                cntError++;
			case EORFOUND:  
//				Control_Reg_CD_Write(0u);
                (*tabSPISel[iSPIDev])(0u);//select low to make sure
    			continueRead = FALSE; 
                
//                continueRead = TRUE;
//				if(0u != (Timer_SelLow_ReadControlRegister() & Timer_SelLow_CTRL_ENABLE ))
//				{
					Timer_SelLow_Stop();
//				}
//				if (0u != (SPIM_BP_STS_SPI_IDLE | SPIM_BP_TX_STATUS_REG))
//				{
					if (0) //(0u !=(SPIM_BP_STS_RX_FIFO_NOT_EMPTY & SPIM_BP_ReadStatus())) //TODO this shouldnt happen Readout any further bytes
					{   
						SPIM_BP_ReadRxData();
//						uint8 tempBuffWrite = buffSPIWrite[iSPIDev];
//						buffSPIWrite[iSPIDev] = WRAPINC(tempBuffWrite, SPI_BUFFER_SIZE);
//						buffSPI[iSPIDev][tempBuffWrite] = SPIM_BP_ReadRxData();
//						buffUsbTx[iBuffUsbTx++] = buffSPI[iSPIDev][tempBuffWrite];
						
					}
					else
					{
//						if (buffSPIRead[iSPIDev] != buffSPIWrite[iSPIDev])
//						{
//							uint8 tempBuffWrite = buffSPIWrite[iSPIDev];
//					
//							uint8 nBytes;
//							
//							if (buffSPIRead[iSPIDev] >= tempBuffWrite)
//							{
//								nBytes = SPI_BUFFER_SIZE - buffSPIRead[iSPIDev];
//								memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][buffSPIRead[iSPIDev]]), nBytes);
//								iBuffUsbTx += nBytes;
//								buffSPIRead[iSPIDev] = 0;
//							}
//							nBytes = tempBuffWrite - buffSPIRead[iSPIDev];
//							memcpy((buffUsbTx + iBuffUsbTx), &(buffSPI[iSPIDev][buffSPIRead[iSPIDev]]), nBytes);
//							iBuffUsbTx += nBytes;
//							buffSPIRead[iSPIDev] = tempBuffWrite;
//						}
						iSPIDev = WRAPINC(iSPIDev, NUM_SPI_DEV);
//						Control_Reg_SS_Write(tabSPISel[iSPIDev]);
//						Control_Reg_CD_Write(1u);
//						(*tabSPISel[iSPIDev])(1u);//select high to check the selected board
						(*tabSPISel[iSPIDev])(0u);//select low and wait
//						lastDrdyCap = Timer_Drdy_ReadPeriod();
						
//						Timer_Drdy_Start();
						readStatusBP = CHECKDATA;
                        loopCountCheck = loopCount;
					}
//				}
				break;
		}
//				if (NewTransmit)
//		{
		CheckI2C();
        CheckRTC();
		//TODO Framing packets
			 /* Service USB CDC when device is configured. */
//		if ((0u != USBUART_CD_GetConfiguration()) )//&& (iBuffUsbTx > 0))
//		{
// 
//			/* Wait until component is ready to send data to host. */
//			if (USBUART_CD_CDCIsReady()) // && ((iBuffUsbTx > 0) || (iBuffUsbTxDebug > 0)))
//			{
////				if ((0 == iBuffUsbTx) && (0 == iBuffUsbTxDebug) && (0 == Pin_BaroPres_Read()) && (0 == Pin_BaroTemp_Read()) && (0 != baroReadReady)) // TODO Temporary barometer read, in future should be a Tsync interrupt
////				{
////					curBaroPresCnt[0] = Counter_BaroPres_ReadCapture();
////					curBaroTempCnt[0] = Counter_BaroTemp_ReadCapture();
////					double U = (double)((double) curBaroTempCnt[0] / (double) BARO_COUNT_TO_US) - baroCE[0].U0;
////					double Tao = (double)((double) curBaroPresCnt[0] / (double) BARO_COUNT_TO_US);
////					curBaroTemp[0] = BaroTempCalc(U, baroCE);
////					curBaroPres[0] = BaroPresCalc(Tao, U, baroCE);
////					uint32 curBaroTempInt = (uint32) curBaroTemp[0];
////					uint32 curBaroPresInt = (uint32) curBaroPres[0];
//////					buffUsbTxDebug[0] = '^';
//////					iBuffUsbTxDebug++;
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (curBaroPresCnt), 4);
//////					iBuffUsbTxDebug += 4;
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (&Tao), sizeof(double));
//////					iBuffUsbTxDebug += sizeof(double);
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (curBaroPres), sizeof(double));
//////					iBuffUsbTxDebug += sizeof(double);
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (&curBaroPresInt), sizeof(uint32));
//////					iBuffUsbTxDebug += sizeof(uint32);
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), "^!", 2);
//////					iBuffUsbTxDebug += 2;
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (curBaroTempCnt), 4);
//////					iBuffUsbTxDebug += 4;
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (&U), sizeof(double));
//////					iBuffUsbTxDebug += sizeof(double);
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (curBaroTemp), sizeof(double));
//////					iBuffUsbTxDebug += sizeof(double);
//////					memcpy((buffUsbTxDebug + iBuffUsbTxDebug), (&curBaroTempInt), sizeof(uint32));
//////					iBuffUsbTxDebug += sizeof(uint32);
//////					buffUsbTxDebug[iBuffUsbTxDebug] = '!';
//////					iBuffUsbTxDebug++;
////					Tao = 1.1; 
////					curBaroPres[0] = 22.22; 
////					U = 333.333;
////					curBaroTemp[0] = 4444.4444;
////					Tao = 2.3E-3;//08;
////					U = 1.7E+3;//08;
////					U /= Tao;
////					iBuffUsbTxDebug = sprintf( (char *) buffUsbTxDebug, "^ %lu, %f, %f^! %lu, %f, %f!", curBaroPresCnt[0], Tao, curBaroPres[0], curBaroTempCnt[0], U, curBaroTemp[0]); //1.1, 22.22, curBaroTempCnt[0], 333.333, 4444.4444);
////					USBUART_CD_PutData(buffUsbTxDebug, iBuffUsbTxDebug);
////					iBuffUsbTxDebug = 0;
////					baroReadReady = 0u;
////					
////				}
////				else if (0 != Pin_BaroPres_Read())
////				{
////					baroReadReady = 1u;
////				}
//				if (iBuffUsbTx > 0)
//				{
////					for(uint8 x = 0; x < iBuffUsbTx; x += USBUART_BUFFER_SIZE)
////					{
////						uint8 iTemp = iBuffUsbTx - x;
////						iTemp = MIN(iTemp, USBUART_BUFFER_SIZE);
////						uint8 tempS[4] = {'m', x, iTemp, 'n'};
////						USBUART_CD_PutData(tempS, 4);
////						while (0 == USBUART_CD_CDCIsReady());
//						USBUART_CD_PutData(buffUsbTx, iBuffUsbTx);
////						if (USBUART_BUFFER_SIZE == iTemp)
////						{
////							CyDelayUs(53333);
////						}
////					}
////					USBUART_CD_PutChar('#');
////					USBUART_CD_PutData((const uint8*)(&(iBuffUsbTx)), 1);
////					char tempS[3];
////					sprintf(tempS,"%i", iBuffUsbTx);
////					USBUART_CD_PutString(tempS);
////					USBUART_CD_PutChar('#');
////					uint8 tempS[3] = {'#', iBuffUsbTx, '#'};
////					while (0 == USBUART_CD_CDCIsReady());
////					USBUART_CD_PutData(tempS, 3);
//					iBuffUsbTx = 0; //TODO handle missed writes
//					
//				}
////				if (iBuffUsbTxDebug > 0)
////				{
////					while (0 == USBUART_CD_CDCIsReady());
////					USBUART_CD_PutData(buffUsbTxDebug, iBuffUsbTxDebug);
////					iBuffUsbTxDebug = 0; //TODO handle missed writes
////				}
//				
//				
//		
//				//iBuffUsbTx = 0;
//			}
//			
//		}
////		else
////		{
		iBuffUsbTx = 0; //TODO handle missed writes
		iBuffUsbTxDebug = 0; //TODO handle missed writes
////		}
//		
//				/* Send data back to host. */
//			   
////				NewTransmit = FALSE;
////
////
////			}
////		}
        loopCount++;
	}
}

/* [] END OF FILE */
