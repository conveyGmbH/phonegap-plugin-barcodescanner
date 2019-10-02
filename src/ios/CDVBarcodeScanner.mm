/*
 * PhoneGap is available under *either* the terms of the modified BSD license *or* the
 * MIT License (2008). See http://opensource.org/licenses/alphabetical for full text.
 *
 * Copyright 2011 Matt Kane. All rights reserved.
 * Copyright (c) 2011, IBM Corporation
 */

#import <Foundation/Foundation.h>
#import <UIKit/UIKit.h>
#import <AVFoundation/AVFoundation.h>
#import <AssetsLibrary/AssetsLibrary.h>
#import <AudioToolbox/AudioToolbox.h>

//------------------------------------------------------------------------------
// use the all-in-one version of zxing that we built
//------------------------------------------------------------------------------
#import "zxing-all-in-one.h"
#import <Cordova/CDVPlugin.h>
#import <Cordova/CDVPlugin+Resources.h>


//------------------------------------------------------------------------------
// Delegate to handle orientation functions
//------------------------------------------------------------------------------
@protocol CDVBarcodeScannerOrientationDelegate <NSObject>

- (NSUInteger)supportedInterfaceOrientations;
- (BOOL)shouldAutorotateToInterfaceOrientation:(UIInterfaceOrientation)interfaceOrientation;
- (BOOL)shouldAutorotate;

@end

//------------------------------------------------------------------------------
// Adds a shutter button to the UI, and changes the scan from continuous to
// only performing a scan when you click the shutter button.  For testing.
//------------------------------------------------------------------------------
#define USE_SHUTTER 0

//------------------------------------------------------------------------------
@class CDVbcsProcessor;
@class CDVbcsZXingProcessor;
@class CDVbcsViewController;

//------------------------------------------------------------------------------
// plugin class
//------------------------------------------------------------------------------
@interface CDVBarcodeScanner : CDVPlugin {}
- (NSString*)isScanNotPossible;
- (void)scan:(CDVInvokedUrlCommand*)command;
- (void)encode:(CDVInvokedUrlCommand*)command;
- (void)returnImage:(NSString*)filePath format:(NSString*)format callback:(NSString*)callback;
- (void)returnSuccess:(NSString*)scannedText format:(NSString*)format cancelled:(BOOL)cancelled flipped:(BOOL)flipped callback:(NSString*)callback;
- (void)returnError:(NSString*)message callback:(NSString*)callback;
@end

//------------------------------------------------------------------------------
// class that does the grunt work
//------------------------------------------------------------------------------
@interface CDVbcsProcessor : NSObject <AVCaptureMetadataOutputObjectsDelegate> {}
@property (nonatomic, retain) CDVBarcodeScanner*           plugin;
@property (nonatomic, retain) NSString*                   callback;
@property (nonatomic, retain) UIViewController*           parentViewController;
@property (nonatomic, retain) CDVbcsViewController*        viewController;
@property (nonatomic, retain) AVCaptureSession*           captureSession;
@property (nonatomic, retain) AVCaptureVideoPreviewLayer* previewLayer;
@property (nonatomic, retain) NSString*                   alternateXib;
@property (nonatomic, retain) NSMutableArray*             results;
@property (nonatomic, retain) NSString*                   formats;
@property (nonatomic)         BOOL                        is1D;
@property (nonatomic)         BOOL                        is2D;
@property (nonatomic)         BOOL                        capturing;
@property (nonatomic)         BOOL                        isFrontCamera;
@property (nonatomic)         BOOL                        isShowFlipCameraButton;
@property (nonatomic)         BOOL                        isShowTorchButton;
@property (nonatomic)         BOOL                        isFlipped;
@property (nonatomic)         BOOL                        isTransitionAnimated;
@property (nonatomic)         BOOL                        isSuccessBeepEnabled;


- (id)initWithPlugin:(CDVBarcodeScanner*)plugin callback:(NSString*)callback parentViewController:(UIViewController*)parentViewController alterateOverlayXib:(NSString *)alternateXib;
- (void)scanBarcode;
- (void)barcodeScanSucceeded:(NSString*)text format:(NSString*)format;
- (void)barcodeScanFailed:(NSString*)message;
- (void)barcodeScanCancelled;
- (void)openDialog;
- (NSString*)setUpCaptureSession;
- (void)captureOutput:(AVCaptureOutput*)captureOutput didOutputMetadataObjects:(NSArray *)metadataObjects fromConnection:(AVCaptureConnection*)connection;
@end

@interface CDVbcsZXingProcessor : NSObject <AVCaptureVideoDataOutputSampleBufferDelegate> {}
@property (nonatomic, retain) CDVBarcodeScanner*          plugin;
@property (nonatomic, retain) NSString*                   callback;
@property (nonatomic, retain) UIViewController*           parentViewController;
@property (nonatomic, retain) CDVbcsViewController*       viewController;
@property (nonatomic, retain) AVCaptureSession*           captureSession;
@property (nonatomic, retain) AVCaptureVideoPreviewLayer* previewLayer;
@property (nonatomic, retain) NSString*                   alternateXib;
@property (nonatomic, retain) NSMutableArray*             results;
@property (nonatomic)         BOOL                        is1D;
@property (nonatomic)         BOOL                        is2D;
@property (nonatomic)         BOOL                        capturing;
@property (nonatomic)         BOOL                        isFrontCamera;
@property (nonatomic)         BOOL                        isFlipped;
@property (nonatomic, retain) AVCaptureDevice*            inputDevice;
@property (nonatomic)         BOOL                        hasToolbarBlack;
@property (nonatomic)         BOOL                        hasToolbarTranslucent;
@property (nonatomic)         NSInteger                   orientationMaskPhone;
@property (nonatomic)         NSInteger                   orientationMaskPad;


- (id)initWithPlugin:(CDVBarcodeScanner*)plugin callback:(NSString*)callback parentViewController:(UIViewController*)parentViewController alterateOverlayXib:(NSString *)alternateXib;
- (void)scanBarcode;
- (void)barcodeScanSucceeded:(NSString*)text format:(NSString*)format;
- (void)barcodeScanFailed:(NSString*)message;
- (void)barcodeScanCancelled;
- (void)openDialog;
- (NSString*)setUpCaptureSession;
- (void)captureOutput:(AVCaptureOutput*)captureOutput didOutputSampleBuffer:(CMSampleBufferRef)sampleBuffer fromConnection:(AVCaptureConnection*)connection;
- (NSString*)formatStringFrom:(zxing::BarcodeFormat)format;
- (UIImage*)getImageFromSample:(CMSampleBufferRef)sampleBuffer;
- (zxing::Ref<zxing::LuminanceSource>) getLuminanceSourceFromSample:(CMSampleBufferRef)sampleBuffer imageArr:(zxing::ArrayRef<char>&)greyArr;
- (UIImage*) getImageFromLuminanceSource:(zxing::LuminanceSource*)luminanceSource;
- (void)dumpImage:(UIImage*)image;
@end

//------------------------------------------------------------------------------
// Qr encoder processor
//------------------------------------------------------------------------------
@interface CDVqrProcessor: NSObject
@property (nonatomic, retain) CDVBarcodeScanner*          plugin;
@property (nonatomic, retain) NSString*                   callback;
@property (nonatomic, retain) NSString*                   stringToEncode;
@property                     NSInteger                   size;

- (id)initWithPlugin:(CDVBarcodeScanner*)plugin callback:(NSString*)callback stringToEncode:(NSString*)stringToEncode;
- (void)generateImage;
@end

//------------------------------------------------------------------------------
// view controller for the ui
//------------------------------------------------------------------------------
@interface CDVbcsViewController : UIViewController <CDVBarcodeScannerOrientationDelegate> {}
@property (nonatomic, retain) CDVbcsProcessor*  processor;
@property (nonatomic, retain) CDVbcsZXingProcessor*  processorZXing;
@property (nonatomic, retain) NSString*        alternateXib;
@property (nonatomic)         BOOL             shutterPressed;
@property (nonatomic, retain) IBOutlet UIView* overlayView;
@property (nonatomic, retain) UIToolbar * toolbar;
@property (nonatomic, retain) UIView * reticleView;
// unsafe_unretained is equivalent to assign - used to prevent retain cycles in the property below
@property (nonatomic, unsafe_unretained) id orientationDelegate;

- (id)initWithProcessor:(CDVbcsProcessor*)processor alternateOverlay:(NSString *)alternateXib;
- (id)initWithZXingProcessor:(CDVbcsZXingProcessor*)processor alternateOverlay:(NSString *)alternateXib;
- (void)startCapturing;
- (UIView*)buildOverlayView;
- (UIImage*)buildReticleImage;
- (void)shutterButtonPressed;
- (IBAction)cancelButtonPressed:(id)sender;
- (IBAction)flipCameraButtonPressed:(id)sender;
- (IBAction)torchButtonPressed:(id)sender;

@end

//------------------------------------------------------------------------------
// plugin class
//------------------------------------------------------------------------------
@implementation CDVBarcodeScanner

//--------------------------------------------------------------------------
- (NSString*)isScanNotPossible {
    NSString* result = nil;

    Class aClass = NSClassFromString(@"AVCaptureSession");
    if (aClass == nil) {
        return @"AVFoundation Framework not available";
    }

    return result;
}

-(BOOL)notHasPermission
{
    AVAuthorizationStatus authStatus = [AVCaptureDevice authorizationStatusForMediaType:AVMediaTypeVideo];
    return (authStatus == AVAuthorizationStatusDenied ||
            authStatus == AVAuthorizationStatusRestricted);
}

-(BOOL)isUsageDescriptionSet
{
  NSDictionary * plist = [[NSBundle mainBundle] infoDictionary];
  if ([plist objectForKey:@"NSCameraUsageDescription" ] ||
      [[NSBundle mainBundle] localizedStringForKey: @"NSCameraUsageDescription" value: nil table: @"InfoPlist"]) {
    return YES;
  }
  return NO;
}



//--------------------------------------------------------------------------
- (void)scan:(CDVInvokedUrlCommand*)command {
    CDVbcsProcessor* processor;
    CDVbcsZXingProcessor* processorZXing;
    NSString*       callback;
    NSString*       capabilityError;

    callback = command.callbackId;

    NSDictionary* options;
    if (command.arguments.count == 0) {
      options = [NSDictionary dictionary];
    } else {
      options = command.arguments[0];
    }

    BOOL preferFrontCamera = [options[@"preferFrontCamera"] boolValue];
    BOOL showFlipCameraButton = [options[@"showFlipCameraButton"] boolValue];
    BOOL showTorchButton = [options[@"showTorchButton"] boolValue];
    BOOL disableAnimations = [options[@"disableAnimations"] boolValue];
    BOOL disableSuccessBeep = [options[@"disableSuccessBeep"] boolValue];
    BOOL hasToolbarBlack = [options[@"BarcodeToolbarBlack"] boolValue];
    BOOL hasToolbarTranslucent = [options[@"BarcodeToolbarTranslucent"] boolValue];
    BOOL orientationMaskPhone = [options[@"BarcodeOrientationMaskPhone"] boolValue];
    BOOL orientationMaskPad = [options[@"BarcodeOrientationMaskPad"] boolValue];
    BOOL useBinaryQrCode = [options[@"useBinaryQrCode"] boolValue];

    // We allow the user to define an alternate xib file for loading the overlay.
    NSString *overlayXib = options[@"overlayXib"];

    capabilityError = [self isScanNotPossible];
    if (capabilityError) {
        [self returnError:capabilityError callback:callback];
        return;
    } else if ([self notHasPermission]) {
        NSString * error = NSLocalizedString(@"Access to the camera has been prohibited; please enable it in the Settings app to continue.",nil);
        [self returnError:error callback:callback];
        return;
    } else if (![self isUsageDescriptionSet]) {
      NSString * error = NSLocalizedString(@"NSCameraUsageDescription is not set in the info.plist", nil);
      [self returnError:error callback:callback];
      return;
    }
    if (useBinaryQrCode) {
      processorZXing = [[CDVbcsZXingProcessor alloc]
                 initWithPlugin:self
                 callback:callback
                 parentViewController:self.viewController
                 alterateOverlayXib:overlayXib
                 ];
      if (hasToolbarBlack) {
        processorZXing.hasToolbarBlack = true;
      }
      if (hasToolbarTranslucent) {
        processorZXing.hasToolbarTranslucent = true;
      }
      if (orientationMaskPhone) {
        processorZXing.orientationMaskPhone = true;
      }
      if (orientationMaskPad) {
        processorZXing.orientationMaskPad = true;
      }

      // queue [processorZXing scanBarcode] to run on the event loop

      if (preferFrontCamera) {
        processorZXing.isFrontCamera = true;
      }

      [processorZXing performSelector:@selector(scanBarcode) withObject:nil afterDelay:0];
    } else {
      processor = [[CDVbcsProcessor alloc]
                initWithPlugin:self
                      callback:callback
          parentViewController:self.viewController
            alterateOverlayXib:overlayXib
            ];
      // queue [processor scanBarcode] to run on the event loop

      if (preferFrontCamera) {
        processor.isFrontCamera = true;
      }

      if (showFlipCameraButton) {
        processor.isShowFlipCameraButton = true;
      }

      if (showTorchButton) {
        processor.isShowTorchButton = true;
      }

      processor.isSuccessBeepEnabled = !disableSuccessBeep;

      processor.isTransitionAnimated = !disableAnimations;

      processor.formats = options[@"formats"];

      [processor performSelector:@selector(scanBarcode) withObject:nil afterDelay:0];

    }
}

//--------------------------------------------------------------------------
- (void)encode:(CDVInvokedUrlCommand*)command {
    if([command.arguments count] < 1)
        [self returnError:@"Too few arguments!" callback:command.callbackId];

    CDVqrProcessor* processor;
    NSString*       callback;
    callback = command.callbackId;

    processor = [[CDVqrProcessor alloc]
                 initWithPlugin:self
                 callback:callback
                 stringToEncode: command.arguments[0][@"data"]
                 ];
    // queue [processor generateImage] to run on the event loop
    [processor performSelector:@selector(generateImage) withObject:nil afterDelay:0];
}

- (void)returnImage:(NSString*)filePath format:(NSString*)format callback:(NSString*)callback{
    NSMutableDictionary* resultDict = [[NSMutableDictionary alloc] init];
    resultDict[@"format"] = format;
    resultDict[@"file"] = filePath;

    CDVPluginResult* result = [CDVPluginResult
                               resultWithStatus: CDVCommandStatus_OK
                               messageAsDictionary:resultDict
                               ];

    [[self commandDelegate] sendPluginResult:result callbackId:callback];
}

//--------------------------------------------------------------------------
- (void)returnSuccess:(NSString*)scannedText format:(NSString*)format cancelled:(BOOL)cancelled flipped:(BOOL)flipped callback:(NSString*)callback{
    NSNumber* cancelledNumber = @(cancelled ? 1 : 0);

    NSMutableDictionary* resultDict = [NSMutableDictionary new];
    resultDict[@"text"] = scannedText;
    resultDict[@"format"] = format;
    resultDict[@"cancelled"] = cancelledNumber;

    CDVPluginResult* result = [CDVPluginResult
                               resultWithStatus: CDVCommandStatus_OK
                               messageAsDictionary: resultDict
                               ];
    [self.commandDelegate sendPluginResult:result callbackId:callback];
}

//--------------------------------------------------------------------------
- (void)returnError:(NSString*)message callback:(NSString*)callback {
    CDVPluginResult* result = [CDVPluginResult
                               resultWithStatus: CDVCommandStatus_ERROR
                               messageAsString: message
                               ];

    [self.commandDelegate sendPluginResult:result callbackId:callback];
}

@end

SystemSoundID _soundFileObject;

//------------------------------------------------------------------------------
// class that does the grunt work
//------------------------------------------------------------------------------
@implementation CDVbcsProcessor

@synthesize plugin               = _plugin;
@synthesize callback             = _callback;
@synthesize parentViewController = _parentViewController;
@synthesize viewController       = _viewController;
@synthesize captureSession       = _captureSession;
@synthesize previewLayer         = _previewLayer;
@synthesize alternateXib         = _alternateXib;
@synthesize is1D                 = _is1D;
@synthesize is2D                 = _is2D;
@synthesize capturing            = _capturing;
@synthesize results              = _results;

//--------------------------------------------------------------------------
- (id)initWithPlugin:(CDVBarcodeScanner*)plugin
            callback:(NSString*)callback
parentViewController:(UIViewController*)parentViewController
  alterateOverlayXib:(NSString *)alternateXib {
    self = [super init];
    if (!self) return self;

    self.plugin               = plugin;
    self.callback             = callback;
    self.parentViewController = parentViewController;
    self.alternateXib         = alternateXib;

    self.is1D      = YES;
    self.is2D      = YES;
    self.capturing = NO;
    self.results = [NSMutableArray new];

    CFURLRef soundFileURLRef  = CFBundleCopyResourceURL(CFBundleGetMainBundle(), CFSTR("CDVBarcodeScanner.bundle/beep"), CFSTR ("caf"), NULL);
    AudioServicesCreateSystemSoundID(soundFileURLRef, &_soundFileObject);

    return self;
}

//--------------------------------------------------------------------------
- (void)dealloc {
    self.plugin = nil;
    self.callback = nil;
    self.parentViewController = nil;
    self.viewController = nil;
    self.captureSession = nil;
    self.previewLayer = nil;
    self.alternateXib = nil;
    self.results = nil;

    self.capturing = NO;

    AudioServicesRemoveSystemSoundCompletion(_soundFileObject);
    AudioServicesDisposeSystemSoundID(_soundFileObject);
}

//--------------------------------------------------------------------------
- (void)scanBarcode {

//    self.captureSession = nil;
//    self.previewLayer = nil;
    NSString* errorMessage = [self setUpCaptureSession];
    if (errorMessage) {
        [self barcodeScanFailed:errorMessage];
        return;
    }

    self.viewController = [[CDVbcsViewController alloc] initWithProcessor: self alternateOverlay:self.alternateXib];
    // here we set the orientation delegate to the MainViewController of the app (orientation controlled in the Project Settings)
    self.viewController.orientationDelegate = self.plugin.viewController;

    // delayed [self openDialog];
    [self performSelector:@selector(openDialog) withObject:nil afterDelay:1];
}

//--------------------------------------------------------------------------
- (void)openDialog {
    [self.viewController setModalPresentationStyle:UIModalPresentationOverFullScreen];
    [self.parentViewController
     presentViewController:self.viewController
     animated:self.isTransitionAnimated completion:nil
     ];
}

//--------------------------------------------------------------------------
- (void)barcodeScanDone:(void (^)(void))callbackBlock {
    self.capturing = NO;
    [self.captureSession stopRunning];
    [self.parentViewController dismissViewControllerAnimated:self.isTransitionAnimated completion:callbackBlock];


    AVCaptureDevice *device = [AVCaptureDevice defaultDeviceWithMediaType:AVMediaTypeVideo];
    [device lockForConfiguration:nil];
    if([device isAutoFocusRangeRestrictionSupported]) {
        [device setAutoFocusRangeRestriction:AVCaptureAutoFocusRangeRestrictionNone];
    }
    [device unlockForConfiguration];

    // viewcontroller holding onto a reference to us, release them so they
    // will release us
    self.viewController = nil;
}

//--------------------------------------------------------------------------
- (BOOL)checkResult:(NSString *)result {
    [self.results addObject:result];

    NSInteger treshold = 7;

    if (self.results.count > treshold) {
        [self.results removeObjectAtIndex:0];
    }

    if (self.results.count < treshold)
    {
        return NO;
    }

    BOOL allEqual = YES;
    NSString *compareString = self.results[0];

    for (NSString *aResult in self.results)
    {
        if (![compareString isEqualToString:aResult])
        {
            allEqual = NO;
            //NSLog(@"Did not fit: %@",self.results);
            break;
        }
    }

    return allEqual;
}

//--------------------------------------------------------------------------
- (void)barcodeScanSucceeded:(NSString*)text format:(NSString*)format {
    dispatch_sync(dispatch_get_main_queue(), ^{
        if (self.isSuccessBeepEnabled) {
            AudioServicesPlaySystemSound(_soundFileObject);
        }
        [self barcodeScanDone:^{
            [self.plugin returnSuccess:text format:format cancelled:FALSE flipped:FALSE callback:self.callback];
        }];
    });
}

//--------------------------------------------------------------------------
- (void)barcodeScanFailed:(NSString*)message {
    dispatch_block_t block = ^{
        [self barcodeScanDone:^{
            [self.plugin returnError:message callback:self.callback];
        }];
    };
    if ([NSThread isMainThread]) {
        block();
    } else {
        dispatch_sync(dispatch_get_main_queue(), block);
    }
}

//--------------------------------------------------------------------------
- (void)barcodeScanCancelled {
    [self barcodeScanDone:^{
        [self.plugin returnSuccess:@"" format:@"" cancelled:TRUE flipped:self.isFlipped callback:self.callback];
    }];
    if (self.isFlipped) {
        self.isFlipped = NO;
    }
}

- (void)flipCamera {
    self.isFlipped = YES;
    self.isFrontCamera = !self.isFrontCamera;
    [self barcodeScanDone:^{
        if (self.isFlipped) {
            self.isFlipped = NO;
        }
    [self performSelector:@selector(scanBarcode) withObject:nil afterDelay:0.1];
    }];
}

- (void)toggleTorch {
  AVCaptureDevice *device = [AVCaptureDevice defaultDeviceWithMediaType:AVMediaTypeVideo];
  [device lockForConfiguration:nil];
  if (device.flashActive) {
    [device setTorchMode:AVCaptureTorchModeOff];
    [device setFlashMode:AVCaptureFlashModeOff];
  } else {
    [device setTorchModeOnWithLevel:AVCaptureMaxAvailableTorchLevel error:nil];
    [device setFlashMode:AVCaptureFlashModeOn];
  }
  [device unlockForConfiguration];
}

//--------------------------------------------------------------------------
- (NSString*)setUpCaptureSession {
    NSError* error = nil;

    AVCaptureSession* captureSession = [[AVCaptureSession alloc] init];
    self.captureSession = captureSession;

       AVCaptureDevice* __block device = nil;
    if (self.isFrontCamera) {

        NSArray* devices = [AVCaptureDevice devicesWithMediaType:AVMediaTypeVideo];
        [devices enumerateObjectsUsingBlock:^(AVCaptureDevice *obj, NSUInteger idx, BOOL *stop) {
            if (obj.position == AVCaptureDevicePositionFront) {
                device = obj;
            }
        }];
    } else {
        device = [AVCaptureDevice defaultDeviceWithMediaType:AVMediaTypeVideo];
        if (!device) return @"unable to obtain video capture device";

    }

    // set focus params if available to improve focusing
    [device lockForConfiguration:&error];
    if (error == nil) {
        if([device isFocusModeSupported:AVCaptureFocusModeContinuousAutoFocus]) {
            [device setFocusMode:AVCaptureFocusModeContinuousAutoFocus];
        }
        if([device isAutoFocusRangeRestrictionSupported]) {
            [device setAutoFocusRangeRestriction:AVCaptureAutoFocusRangeRestrictionNear];
        }
    }
    [device unlockForConfiguration];

    AVCaptureDeviceInput* input = [AVCaptureDeviceInput deviceInputWithDevice:device error:&error];
    if (!input) return @"unable to obtain video capture device input";

    AVCaptureMetadataOutput* output = [[AVCaptureMetadataOutput alloc] init];
    if (!output) return @"unable to obtain video capture output";

    [output setMetadataObjectsDelegate:self queue:dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_LOW, 0)];

    if ([captureSession canSetSessionPreset:AVCaptureSessionPresetHigh]) {
      captureSession.sessionPreset = AVCaptureSessionPresetHigh;
    } else if ([captureSession canSetSessionPreset:AVCaptureSessionPresetMedium]) {
      captureSession.sessionPreset = AVCaptureSessionPresetMedium;
    } else {
      return @"unable to preset high nor medium quality video capture";
    }

    if ([captureSession canAddInput:input]) {
        [captureSession addInput:input];
    }
    else {
        return @"unable to add video capture device input to session";
    }

    if ([captureSession canAddOutput:output]) {
        [captureSession addOutput:output];
    }
    else {
        return @"unable to add video capture output to session";
    }

    [output setMetadataObjectTypes:[self formatObjectTypes]];

    // setup capture preview layer
    self.previewLayer = [AVCaptureVideoPreviewLayer layerWithSession:captureSession];
    self.previewLayer.videoGravity = AVLayerVideoGravityResizeAspectFill;

    // run on next event loop pass [captureSession startRunning]
    [captureSession performSelector:@selector(startRunning) withObject:nil afterDelay:0];

    return nil;
}

//--------------------------------------------------------------------------
// this method gets sent the captured frames
//--------------------------------------------------------------------------
- (void)captureOutput:(AVCaptureOutput*)captureOutput didOutputMetadataObjects:(NSArray *)metadataObjects fromConnection:(AVCaptureConnection*)connection {

    if (!self.capturing) return;

#if USE_SHUTTER
    if (!self.viewController.shutterPressed) return;
    self.viewController.shutterPressed = NO;

    UIView* flashView = [[UIView alloc] initWithFrame:self.viewController.view.frame];
    [flashView setBackgroundColor:[UIColor whiteColor]];
    [self.viewController.view.window addSubview:flashView];

    [UIView
     animateWithDuration:.4f
     animations:^{
         [flashView setAlpha:0.f];
     }
     completion:^(BOOL finished){
         [flashView removeFromSuperview];
     }
     ];
#endif


    try {
        // This will bring in multiple entities if there are multiple 2D codes in frame.
        for (AVMetadataObject *metaData in metadataObjects) {
            AVMetadataMachineReadableCodeObject* code = (AVMetadataMachineReadableCodeObject*)[self.previewLayer transformedMetadataObjectForMetadataObject:(AVMetadataMachineReadableCodeObject*)metaData];

            if ([self checkResult:code.stringValue]) {
                [self barcodeScanSucceeded:code.stringValue format:[self formatStringFromMetadata:code]];
            }
        }
    }
    catch (...) {
        //            NSLog(@"decoding: unknown exception");
        //            [self barcodeScanFailed:@"unknown exception decoding barcode"];
    }

    //        NSTimeInterval timeElapsed  = [NSDate timeIntervalSinceReferenceDate] - timeStart;
    //        NSLog(@"decoding completed in %dms", (int) (timeElapsed * 1000));

}

//--------------------------------------------------------------------------
// convert metadata object information to barcode format string
//--------------------------------------------------------------------------
- (NSString*)formatStringFromMetadata:(AVMetadataMachineReadableCodeObject*)format {
    if (format.type == AVMetadataObjectTypeQRCode)          return @"QR_CODE";
    if (format.type == AVMetadataObjectTypeAztecCode)       return @"AZTEC";
    if (format.type == AVMetadataObjectTypeDataMatrixCode)  return @"DATA_MATRIX";
    if (format.type == AVMetadataObjectTypeUPCECode)        return @"UPC_E";
    // According to Apple documentation, UPC_A is EAN13 with a leading 0.
    if (format.type == AVMetadataObjectTypeEAN13Code && [format.stringValue characterAtIndex:0] == '0') return @"UPC_A";
    if (format.type == AVMetadataObjectTypeEAN8Code)        return @"EAN_8";
    if (format.type == AVMetadataObjectTypeEAN13Code)       return @"EAN_13";
    if (format.type == AVMetadataObjectTypeCode128Code)     return @"CODE_128";
    if (format.type == AVMetadataObjectTypeCode93Code)      return @"CODE_93";
    if (format.type == AVMetadataObjectTypeCode39Code)      return @"CODE_39";
    if (format.type == AVMetadataObjectTypeInterleaved2of5Code) return @"ITF";
    if (format.type == AVMetadataObjectTypeITF14Code)          return @"ITF_14";

    if (format.type == AVMetadataObjectTypePDF417Code)      return @"PDF_417";
    return @"???";
}

//--------------------------------------------------------------------------
// convert string formats to metadata objects
//--------------------------------------------------------------------------
- (NSArray*) formatObjectTypes {
    NSArray *supportedFormats = nil;
    if (self.formats != nil) {
        supportedFormats = [self.formats componentsSeparatedByString:@","];
    }

    NSMutableArray * formatObjectTypes = [NSMutableArray array];

    if (self.formats == nil || [supportedFormats containsObject:@"QR_CODE"]) [formatObjectTypes addObject:AVMetadataObjectTypeQRCode];
    if (self.formats == nil || [supportedFormats containsObject:@"AZTEC"]) [formatObjectTypes addObject:AVMetadataObjectTypeAztecCode];
    if (self.formats == nil || [supportedFormats containsObject:@"DATA_MATRIX"]) [formatObjectTypes addObject:AVMetadataObjectTypeDataMatrixCode];
    if (self.formats == nil || [supportedFormats containsObject:@"UPC_E"]) [formatObjectTypes addObject:AVMetadataObjectTypeUPCECode];
    if (self.formats == nil || [supportedFormats containsObject:@"EAN_8"]) [formatObjectTypes addObject:AVMetadataObjectTypeEAN8Code];
    if (self.formats == nil || [supportedFormats containsObject:@"EAN_13"]) [formatObjectTypes addObject:AVMetadataObjectTypeEAN13Code];
    if (self.formats == nil || [supportedFormats containsObject:@"CODE_128"]) [formatObjectTypes addObject:AVMetadataObjectTypeCode128Code];
    if (self.formats == nil || [supportedFormats containsObject:@"CODE_93"]) [formatObjectTypes addObject:AVMetadataObjectTypeCode93Code];
    if (self.formats == nil || [supportedFormats containsObject:@"CODE_39"]) [formatObjectTypes addObject:AVMetadataObjectTypeCode39Code];
    if (self.formats == nil || [supportedFormats containsObject:@"ITF"]) [formatObjectTypes addObject:AVMetadataObjectTypeInterleaved2of5Code];
    if (self.formats == nil || [supportedFormats containsObject:@"ITF_14"]) [formatObjectTypes addObject:AVMetadataObjectTypeITF14Code];
    if (self.formats == nil || [supportedFormats containsObject:@"PDF_417"]) [formatObjectTypes addObject:AVMetadataObjectTypePDF417Code];

    return formatObjectTypes;
}

@end

//------------------------------------------------------------------------------
// class that does the grunt work
//------------------------------------------------------------------------------
@implementation CDVbcsZXingProcessor
{
    NSInteger cycle;
}

@synthesize plugin               = _plugin;
@synthesize callback             = _callback;
@synthesize parentViewController = _parentViewController;
@synthesize viewController       = _viewController;
@synthesize captureSession       = _captureSession;
@synthesize previewLayer         = _previewLayer;
@synthesize alternateXib         = _alternateXib;
@synthesize is1D                 = _is1D;
@synthesize is2D                 = _is2D;
@synthesize capturing            = _capturing;
@synthesize results              = _results;
@synthesize inputDevice          = _inputDevice;

//--------------------------------------------------------------------------
- (id)initWithPlugin:(CDVBarcodeScanner*)plugin
            callback:(NSString*)callback
parentViewController:(UIViewController*)parentViewController
  alterateOverlayXib:(NSString *)alternateXib {
    self = [super init];
    if (!self) return self;
    
    self.plugin               = plugin;
    self.callback             = callback;
    self.parentViewController = parentViewController;
    self.alternateXib         = alternateXib;
    
    self.is1D      = YES;
    self.is2D      = YES;
    self.capturing = NO;
    self.results   = [NSMutableArray new];
    
    self.hasToolbarBlack       = NO;
    self.hasToolbarTranslucent = NO;
    self.orientationMaskPhone  = 0;
    self.orientationMaskPad    = 0;
    
    cycle = 0;
    
    CFURLRef soundFileURLRef = CFBundleCopyResourceURL(CFBundleGetMainBundle(), CFSTR("CDVBarcodeScanner.bundle/beep"), CFSTR ("caf"), NULL);
    AudioServicesCreateSystemSoundID(soundFileURLRef, &_soundFileObject);
    CFRelease(soundFileURLRef);
    
    return self;
}

//--------------------------------------------------------------------------
- (void)dealloc {
    self.plugin = nil;
    self.callback = nil;
    self.parentViewController = nil;
    self.viewController = nil;
    self.captureSession = nil;
    self.previewLayer = nil;
    self.alternateXib = nil;
    self.results = nil;
    self.inputDevice = nil;
    
    self.capturing = NO;
    
    AudioServicesRemoveSystemSoundCompletion(_soundFileObject);
    AudioServicesDisposeSystemSoundID(_soundFileObject);
}

//--------------------------------------------------------------------------
- (void)scanBarcode {
    
//    self.captureSession = nil;
//    self.previewLayer = nil;
    NSString* errorMessage = [self setUpCaptureSession];
    if (errorMessage) {
        [self barcodeScanFailed:errorMessage];
        return;
    }
    
    self.viewController = [[CDVbcsViewController alloc] initWithZXingProcessor: self alternateOverlay:self.alternateXib];
    // here we set the orientation delegate to the MainViewController of the app (orientation controlled in the Project Settings)
    self.viewController.orientationDelegate = self.plugin.viewController;
    
    // delayed [self openDialog];
    [self performSelector:@selector(openDialog) withObject:nil afterDelay:1];
}

//--------------------------------------------------------------------------
- (void)openDialog {
    [self.viewController setModalPresentationStyle:UIModalPresentationOverFullScreen];
    [self.parentViewController
     presentViewController:self.viewController
     animated:YES completion:nil
     ];
}

//--------------------------------------------------------------------------
- (void)barcodeScanDone {
    self.capturing = NO;
    [self.captureSession stopRunning];
    [self.parentViewController dismissViewControllerAnimated:YES completion:nil];
    
    // viewcontroller holding onto a reference to us, release them so they
    // will release us
    self.viewController = nil;
}

//--------------------------------------------------------------------------
- (BOOL)checkResult:(NSString *)result {
    [self.results addObject:result];
    
    NSInteger treshold = 5;
    
    if (self.results.count > treshold) {
        [self.results removeObjectAtIndex:0];
    }
    
    if (self.results.count < treshold)
    {
        return NO;
    }
    
    BOOL allEqual = YES;
    NSString *compareString = [self.results objectAtIndex:0];
    
    for (NSString *aResult in self.results)
    {
        if (![compareString isEqualToString:aResult])
        {
            allEqual = NO;
            //NSLog(@"Did not fit: %@",self.results);
            break;
        }
    }
    
    return allEqual;
}

//--------------------------------------------------------------------------
- (void)barcodeScanSucceeded:(NSString*)text format:(NSString*)format {
    dispatch_sync(dispatch_get_main_queue(), ^{
        [self barcodeScanDone];
        AudioServicesPlaySystemSound(_soundFileObject);
        [self.plugin returnSuccess:text format:format cancelled:FALSE flipped:FALSE callback:self.callback];
    });
}

//--------------------------------------------------------------------------
- (void)barcodeScanFailed:(NSString*)message {
    [self barcodeScanDone];
    [self.plugin returnError:message callback:self.callback];
}

//--------------------------------------------------------------------------
- (void)barcodeScanCancelled {
    [self barcodeScanDone];
    [self.plugin returnSuccess:@"" format:@"" cancelled:TRUE flipped:self.isFlipped callback:self.callback];
    if (self.isFlipped) {
        self.isFlipped = NO;
    }
}


- (void)flipCamera
{
    self.isFlipped = YES;
    self.isFrontCamera = !self.isFrontCamera;
    [self performSelector:@selector(barcodeScanCancelled) withObject:nil afterDelay:0];
    [self performSelector:@selector(scanBarcode) withObject:nil afterDelay:0.1];
}

//--------------------------------------------------------------------------
- (NSString*)setUpCaptureSession {
    NSError* error = nil;
    
    AVCaptureSession* captureSession = [[AVCaptureSession alloc] init];
    self.captureSession = captureSession;
    
    self.inputDevice = nil;
    if (self.isFrontCamera) {
        NSArray* devices = [AVCaptureDevice devicesWithMediaType:AVMediaTypeVideo];
        [devices enumerateObjectsUsingBlock:^(AVCaptureDevice *obj, NSUInteger idx, BOOL *stop) {
            if (obj.position == AVCaptureDevicePositionFront) {
                self.inputDevice = obj;
            }
        }];
    }
    else {
        self.inputDevice = [AVCaptureDevice defaultDeviceWithMediaType:AVMediaTypeVideo];
    }
    if (!self.inputDevice) return @"unable to obtain video capture device";
    
    // set focus params if available to improve focusing
    [self.inputDevice lockForConfiguration:&error];
    if (error == nil) {
        if([self.inputDevice isFocusModeSupported:AVCaptureFocusModeContinuousAutoFocus]) {
            [self.inputDevice setFocusMode:AVCaptureFocusModeContinuousAutoFocus];
        }
        if([self.inputDevice isAutoFocusRangeRestrictionSupported]) {
            [self.inputDevice setAutoFocusRangeRestriction:AVCaptureAutoFocusRangeRestrictionNear];
        }
    }
    [self.inputDevice unlockForConfiguration];
    
    AVCaptureDeviceInput* input = [AVCaptureDeviceInput deviceInputWithDevice:self.inputDevice error:&error];
    if (!input) {
        return @"unable to obtain video capture device input";
    }
    
    AVCaptureVideoDataOutput* output = [[AVCaptureVideoDataOutput alloc] init];
    if (!output) return @"unable to obtain video capture output";

    NSDictionary* videoOutputSettings = [NSDictionary
                                         dictionaryWithObject:[NSNumber numberWithInt:kCVPixelFormatType_32BGRA]
                                         forKey:(id)kCVPixelBufferPixelFormatTypeKey
                                         ];
    
    output.alwaysDiscardsLateVideoFrames = YES;
    output.videoSettings = videoOutputSettings;
    
    [output setSampleBufferDelegate:self queue:dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_LOW, 0)];
    
    if ([captureSession canSetSessionPreset:AVCaptureSessionPresetHigh]) {
        captureSession.sessionPreset = AVCaptureSessionPresetHigh;
    }
    else {
        return @"unable to preset high quality video capture";
    }
    
    if ([captureSession canAddInput:input]) {
        [captureSession addInput:input];
    }
    else {
        return @"unable to add video capture device input to session";
    }
    
    if ([captureSession canAddOutput:output]) {
        [captureSession addOutput:output];
    }
    else {
        return @"unable to add video capture output to session";
    }
    
    // setup capture preview layer
    self.previewLayer = [AVCaptureVideoPreviewLayer layerWithSession:captureSession];
    
    // run on next event loop pass [captureSession startRunning]
    [captureSession performSelector:@selector(startRunning) withObject:nil afterDelay:0];
    
    return nil;
}

//--------------------------------------------------------------------------
// this method gets sent the captured frames
//--------------------------------------------------------------------------
- (void)captureOutput:(AVCaptureOutput*)captureOutput didOutputSampleBuffer:(CMSampleBufferRef)sampleBuffer fromConnection:(AVCaptureConnection*)connection {
    
    if (!self.capturing) return;
    
#if USE_SHUTTER
    if (!self.viewController.shutterPressed) return;
    self.viewController.shutterPressed = NO;
    
    UIView* flashView = [[UIView alloc] initWithFrame:self.viewController.view.frame];
    [flashView setBackgroundColor:[UIColor whiteColor]];
    [self.viewController.view.window addSubview:flashView];
    
    [UIView
     animateWithDuration:.4f
     animations:^{
         [flashView setAlpha:0.f];
     }
     completion:^(BOOL finished){
         [flashView removeFromSuperview];
     }
     ];
    
    //         [self dumpImage: [self getImageFromSample:sampleBuffer]];
#endif
    
    
    using namespace zxing;
    
    // LuminanceSource is pretty dumb; we have to give it a pointer to
    // a byte array, but then can't get it back out again.  We need to
    // get it back to free it.  Saving it in imageBytes.
    ArrayRef<char> imageArr;
    
    //        NSTimeInterval timeStart = [NSDate timeIntervalSinceReferenceDate];
    
    try {
        DecodeHints decodeHints;
        decodeHints.addFormat(zxing::BarcodeFormat::AZTEC);
        decodeHints.addFormat(zxing::BarcodeFormat::CODABAR);
        decodeHints.addFormat(zxing::BarcodeFormat::CODE_39);
        decodeHints.addFormat(zxing::BarcodeFormat::CODE_93);
        decodeHints.addFormat(zxing::BarcodeFormat::CODE_128);
        decodeHints.addFormat(zxing::BarcodeFormat::DATA_MATRIX);
        decodeHints.addFormat(zxing::BarcodeFormat::EAN_8);
        decodeHints.addFormat(zxing::BarcodeFormat::EAN_13);
        decodeHints.addFormat(zxing::BarcodeFormat::ITF);
        decodeHints.addFormat(zxing::BarcodeFormat::MAXICODE);
        decodeHints.addFormat(zxing::BarcodeFormat::PDF_417);
        decodeHints.addFormat(zxing::BarcodeFormat::QR_CODE);
        decodeHints.addFormat(zxing::BarcodeFormat::RSS_14);
        decodeHints.addFormat(zxing::BarcodeFormat::RSS_EXPANDED);
        decodeHints.addFormat(zxing::BarcodeFormat::UPC_A);
        decodeHints.addFormat(zxing::BarcodeFormat::UPC_E);
        decodeHints.addFormat(zxing::BarcodeFormat::UPC_EAN_EXTENSION);
        
        // here's the meat of the decode process
        Ref<LuminanceSource>   luminanceSource   ([self getLuminanceSourceFromSample: sampleBuffer imageArr:imageArr]);
        //            [self dumpImage: [self getImageFromLuminanceSource:luminanceSource]];
        Ref<Binarizer>         binarizer         (new HybridBinarizer(luminanceSource));
        Ref<BinaryBitmap>      bitmap            (new BinaryBitmap(binarizer));
        Ref<MultiFormatReader> reader            (new MultiFormatReader());
        Ref<Result>            result            (reader->decode(bitmap, decodeHints));
        Ref<String>            resultText        (result->getText());
        BarcodeFormat          formatVal =       result->getBarcodeFormat();
        NSString*              format    =       [self formatStringFrom:formatVal];
        
        
        const char* cString      = resultText->getText().c_str();
        NSString*   resultString = [[NSString alloc] initWithCString:cString encoding:NSUTF8StringEncoding];
        
        if ([self checkResult:resultString]) {
            [self barcodeScanSucceeded:resultString format:format];
        }
        
        
        
    }
    catch (zxing::ReaderException &rex) {
        //            NSString *message = [[NSString alloc] initWithCString:rex.what() encoding:NSUTF8StringEncoding];
        //            NSLog(@"decoding: ReaderException: %@", message);
    }
    catch (zxing::IllegalArgumentException &iex) {
        //            NSString *message = [[NSString alloc] initWithCString:iex.what() encoding:NSUTF8StringEncoding];
        //            NSLog(@"decoding: IllegalArgumentException: %@", message);
    }
    catch (...) {
        //            NSLog(@"decoding: unknown exception");
        //            [self barcodeScanFailed:@"unknown exception decoding barcode"];
    }
    
    //        NSTimeInterval timeElapsed  = [NSDate timeIntervalSinceReferenceDate] - timeStart;
    //        NSLog(@"decoding completed in %dms", (int) (timeElapsed * 1000));
    
    // free the buffer behind the LuminanceSource
    imageArr.reset(nil);
}

//--------------------------------------------------------------------------
// convert barcode format to string
//--------------------------------------------------------------------------
- (NSString*)formatStringFrom:(zxing::BarcodeFormat)format {
    if (format == zxing::BarcodeFormat::AZTEC)              return @"AZTEC";
    if (format == zxing::BarcodeFormat::CODABAR)            return @"CODABAR";
    if (format == zxing::BarcodeFormat::CODE_39)            return @"CODE_39";
    if (format == zxing::BarcodeFormat::CODE_93)            return @"CODE_93";
    if (format == zxing::BarcodeFormat::CODE_128)           return @"CODE_128";
    if (format == zxing::BarcodeFormat::DATA_MATRIX)        return @"DATA_MATRIX";
    if (format == zxing::BarcodeFormat::EAN_8)              return @"EAN_8";
    if (format == zxing::BarcodeFormat::EAN_13)             return @"EAN_13";
    if (format == zxing::BarcodeFormat::ITF)                return @"ITF";
    if (format == zxing::BarcodeFormat::MAXICODE)           return @"MAXICODE";
    if (format == zxing::BarcodeFormat::PDF_417)            return @"PDF_417";
    if (format == zxing::BarcodeFormat::QR_CODE)            return @"QR_CODE";
    if (format == zxing::BarcodeFormat::RSS_14)             return @"RSS_14";
    if (format == zxing::BarcodeFormat::RSS_EXPANDED)       return @"RSS_EXPANDED";
    if (format == zxing::BarcodeFormat::UPC_A)              return @"UPC_A";
    if (format == zxing::BarcodeFormat::UPC_E)              return @"UPC_E";
    if (format == zxing::BarcodeFormat::UPC_EAN_EXTENSION)  return @"UPC_EAN_EXTENSION";
    return @"???";
}

//--------------------------------------------------------------------------
// convert capture's sample buffer (scanned picture) into the thing that
// zxing needs.
//--------------------------------------------------------------------------
- (zxing::Ref<zxing::LuminanceSource>) getLuminanceSourceFromSample:(CMSampleBufferRef)sampleBuffer imageArr:(zxing::ArrayRef<char>&)greyArr {
    UIInterfaceOrientation ori = [[UIApplication sharedApplication] statusBarOrientation];
    
    CVImageBufferRef imageBuffer = CMSampleBufferGetImageBuffer(sampleBuffer);
    CVPixelBufferLockBaseAddress(imageBuffer, 0);
    
    size_t   bytesPerRow =            CVPixelBufferGetBytesPerRow(imageBuffer);
    size_t   width       =            CVPixelBufferGetWidth(imageBuffer);
    size_t   height      =            CVPixelBufferGetHeight(imageBuffer);
    uint8_t* baseAddress = (uint8_t*) CVPixelBufferGetBaseAddress(imageBuffer);
    
    // only going to get 90% of the width/height of the captured image
    size_t    greyHeight = 9 * MIN(width, height) / 10
    ,         greyWidth  = UIInterfaceOrientationIsLandscape(ori) ? 9 * MAX(width, height) / 10 : greyHeight;
    int arrSize = (int)(greyWidth * greyHeight);
    greyArr = new zxing::Array<char>(arrSize);
    
    if (!greyArr->values().data()) {
        CVPixelBufferUnlockBaseAddress(imageBuffer,0);
        throw new zxing::ReaderException("out of memory");
    }
    
    size_t offsetX = (width  - greyWidth) / 2;
    size_t offsetY = (height - greyHeight) / 2;
    
    // pixel-by-pixel ...
    for (size_t i=0; i<greyWidth; i++) {
        for (size_t j=0; j<greyHeight; j++) {
            // i,j are the coordinates from the sample buffer
            // ni, nj are the coordinates in the LuminanceSource
            // in this case, there's a rotation taking place
            size_t ni = greyHeight-j;
            size_t nj = i;
            
            size_t baseOffset = (j+offsetY)*bytesPerRow + (i + offsetX)*4;
            
            // convert from color to grayscale
            // http://en.wikipedia.org/wiki/Grayscale#Converting_color_to_grayscale
            size_t value = 0.11 * baseAddress[baseOffset] +
            0.59 * baseAddress[baseOffset + 1] +
            0.30 * baseAddress[baseOffset + 2];
            
            int idx = (int)(nj*greyHeight + ni);
            greyArr[idx] = value;
        }
    }
    
    CVPixelBufferUnlockBaseAddress(imageBuffer,0);
    
    using namespace zxing;
    
    Ref<LuminanceSource> luminanceSource (new GreyscaleLuminanceSource(greyArr,
                                                                       (int)greyHeight, (int)greyWidth,
                                                                       0, 0,
                                                                       (int)greyHeight, (int)greyWidth,
                                                                       (cycle++ % 5 == 0))
                                          );
    
    return luminanceSource;
}

//--------------------------------------------------------------------------
// for debugging
//--------------------------------------------------------------------------
- (UIImage*) getImageFromLuminanceSource:(zxing::LuminanceSource*)luminanceSource  {
    zxing::ArrayRef<char> chararr = luminanceSource->getMatrix();
    char* bytes = chararr->values().data();
    CGColorSpaceRef colorSpace = CGColorSpaceCreateDeviceGray();
    CGContextRef context = CGBitmapContextCreate(
                                                 bytes,
                                                 luminanceSource->getWidth(), luminanceSource->getHeight(), 8, luminanceSource->getWidth(),
                                                 colorSpace,
                                                 kCGImageAlphaNone
                                                 );
    
    CGImageRef cgImage = CGBitmapContextCreateImage(context);
    UIImage*   image   = [[UIImage alloc] initWithCGImage:cgImage];
    
    CGContextRelease(context);
    CGColorSpaceRelease(colorSpace);
    CGImageRelease(cgImage);
    free(bytes);
    
    return image;
}

//--------------------------------------------------------------------------
// for debugging
//--------------------------------------------------------------------------
- (UIImage*)getImageFromSample:(CMSampleBufferRef)sampleBuffer {
    CVImageBufferRef imageBuffer = CMSampleBufferGetImageBuffer(sampleBuffer);
    CVPixelBufferLockBaseAddress(imageBuffer, 0);
    
    size_t bytesPerRow = CVPixelBufferGetBytesPerRow(imageBuffer);
    size_t width       = CVPixelBufferGetWidth(imageBuffer);
    size_t height      = CVPixelBufferGetHeight(imageBuffer);
    
    uint8_t* baseAddress    = (uint8_t*) CVPixelBufferGetBaseAddress(imageBuffer);
    int      length         = (int)(height * bytesPerRow);
    uint8_t* newBaseAddress = (uint8_t*) malloc(length);
    memcpy(newBaseAddress, baseAddress, length);
    baseAddress = newBaseAddress;
    
    CGColorSpaceRef colorSpace = CGColorSpaceCreateDeviceRGB();
    CGContextRef context = CGBitmapContextCreate(
                                                 baseAddress,
                                                 width, height, 8, bytesPerRow,
                                                 colorSpace,
                                                 kCGBitmapByteOrder32Little | kCGImageAlphaNoneSkipFirst
                                                 );
    
    CGImageRef cgImage = CGBitmapContextCreateImage(context);
    UIImage*   image   = [[UIImage alloc] initWithCGImage:cgImage];
    
    CVPixelBufferUnlockBaseAddress(imageBuffer,0);
    CGContextRelease(context);
    CGColorSpaceRelease(colorSpace);
    CGImageRelease(cgImage);
    
    free(baseAddress);
    
    return image;
}

//--------------------------------------------------------------------------
// for debugging
//--------------------------------------------------------------------------
- (void)dumpImage:(UIImage*)image {
    NSLog(@"writing image to library: %dx%d", (int)image.size.width, (int)image.size.height);
    ALAssetsLibrary* assetsLibrary = [[ALAssetsLibrary alloc] init];
    [assetsLibrary
     writeImageToSavedPhotosAlbum:image.CGImage
     orientation:ALAssetOrientationUp
     completionBlock:^(NSURL* assetURL, NSError* error){
         if (error) NSLog(@"   error writing image to library");
         else       NSLog(@"   wrote image to library %@", assetURL);
     }
     ];
}

@end

//------------------------------------------------------------------------------
// qr encoder processor
//------------------------------------------------------------------------------
@implementation CDVqrProcessor
@synthesize plugin               = _plugin;
@synthesize callback             = _callback;
@synthesize stringToEncode       = _stringToEncode;
@synthesize size                 = _size;

- (id)initWithPlugin:(CDVBarcodeScanner*)plugin callback:(NSString*)callback stringToEncode:(NSString*)stringToEncode{
    self = [super init];
    if (!self) return self;

    self.plugin          = plugin;
    self.callback        = callback;
    self.stringToEncode  = stringToEncode;
    self.size            = 300;

    return self;
}

//--------------------------------------------------------------------------
- (void)dealloc {
    self.plugin = nil;
    self.callback = nil;
    self.stringToEncode = nil;
}

//--------------------------------------------------------------------------
- (void)generateImage{
    /* setup qr filter */
    CIFilter *filter = [CIFilter filterWithName:@"CIQRCodeGenerator"];
    [filter setDefaults];

    /* set filter's input message
     * the encoding string has to be convert to a UTF-8 encoded NSData object */
    [filter setValue:[self.stringToEncode dataUsingEncoding:NSUTF8StringEncoding]
              forKey:@"inputMessage"];

    /* on ios >= 7.0  set low image error correction level */
    if (floor(NSFoundationVersionNumber) >= NSFoundationVersionNumber_iOS_7_0)
        [filter setValue:@"L" forKey:@"inputCorrectionLevel"];

    /* prepare cgImage */
    CIImage *outputImage = [filter outputImage];
    CIContext *context = [CIContext contextWithOptions:nil];
    CGImageRef cgImage = [context createCGImage:outputImage
                                       fromRect:[outputImage extent]];

    /* returned qr code image */
    UIImage *qrImage = [UIImage imageWithCGImage:cgImage
                                           scale:1.
                                     orientation:UIImageOrientationUp];
    /* resize generated image */
    CGFloat width = _size;
    CGFloat height = _size;

    UIGraphicsBeginImageContext(CGSizeMake(width, height));

    CGContextRef ctx = UIGraphicsGetCurrentContext();
    CGContextSetInterpolationQuality(ctx, kCGInterpolationNone);
    [qrImage drawInRect:CGRectMake(0, 0, width, height)];
    qrImage = UIGraphicsGetImageFromCurrentImageContext();

    /* clean up */
    UIGraphicsEndImageContext();
    CGImageRelease(cgImage);

    /* save image to file */
    NSString* fileName = [[[NSProcessInfo processInfo] globallyUniqueString] stringByAppendingString:@".jpg"];
    NSString* filePath = [NSTemporaryDirectory() stringByAppendingPathComponent:fileName];
    [UIImageJPEGRepresentation(qrImage, 1.0) writeToFile:filePath atomically:YES];

    /* return file path back to cordova */
    [self.plugin returnImage:filePath format:@"QR_CODE" callback: self.callback];
}
@end

//------------------------------------------------------------------------------
// view controller for the ui
//------------------------------------------------------------------------------
@implementation CDVbcsViewController
{
    UIBarButtonItem *switchTorchBtn;
}
@synthesize processor      = _processor;
@synthesize processorZXing = _processorZXing;
@synthesize shutterPressed = _shutterPressed;
@synthesize alternateXib   = _alternateXib;
@synthesize overlayView    = _overlayView;

//--------------------------------------------------------------------------
- (id)initWithProcessor:(CDVbcsProcessor*)processor alternateOverlay:(NSString *)alternateXib {
    self = [super init];
    if (!self) return self;

    self.processor = processor;
    self.shutterPressed = NO;
    self.alternateXib = alternateXib;
    self.overlayView = nil;
    return self;
}
- (id)initWithZXingProcessor:(CDVbcsZXingProcessor*)processor alternateOverlay:(NSString *)alternateXib {
    self = [super init];
    if (!self) return self;

    self.processorZXing = processor;
    self.shutterPressed = NO;
    self.alternateXib = alternateXib;
    self.overlayView = nil;
    return self;
}

//--------------------------------------------------------------------------
- (void)dealloc {
    self.view = nil;
    self.processor = nil;
    self.processorZXing = nil;
    self.shutterPressed = NO;
    self.alternateXib = nil;
    self.overlayView = nil;
    switchTorchBtn = nil;
}

//--------------------------------------------------------------------------
- (void)loadView {
    if (self.processorZXing)
        self.view = [[UIView alloc] init];
    else if (self.processor)
        self.view = [[UIView alloc] initWithFrame: self.processor.parentViewController.view.frame];
}

//--------------------------------------------------------------------------
- (void)viewWillAppear:(BOOL)animated {
    if (self.processorZXing) {
        [super viewWillAppear:animated];

        // it can happen that self and/or parent don't support all/the same orientations
        // and therefore eventually differ in orientation
        UIInterfaceOrientation ori =[[UIApplication sharedApplication] statusBarOrientation];
        CGRect theFrame = self.processorZXing.parentViewController.view.frame;
        CGFloat w = theFrame.size.width
        ,       h = theFrame.size.height
        ,       l = MAX(w, h)
        ,       s = MIN(w, h);
    
        if (UIInterfaceOrientationIsPortrait(ori)) {
            w = s;
            h = l;
        }
        else {
            w = l;
            h = s;
        }
        theFrame = CGRectMake(0.0, 0.0, w, h);
        self.view.frame = theFrame;

        // setup capture preview layer
        AVCaptureVideoPreviewLayer* previewLayer = self.processorZXing.previewLayer;
        previewLayer.frame = theFrame;
        previewLayer.videoGravity = AVLayerVideoGravityResizeAspectFill;
    
        if ([previewLayer.connection isVideoOrientationSupported]) {
            // set video orientation to what the camera sees
            [previewLayer.connection setVideoOrientation:ori];
        }
    
        [self.view.layer insertSublayer:previewLayer below:[[self.view.layer sublayers] objectAtIndex:0]];
    
        [self.view addSubview:[self buildOverlayView]];
    } else if (self.processor) {
        // set video orientation to what the camera sees
        self.processor.previewLayer.connection.videoOrientation = [self interfaceOrientationToVideoOrientation:[UIApplication sharedApplication].statusBarOrientation];
        
        // this fixes the bug when the statusbar is landscape, and the preview layer
        // starts up in portrait (not filling the whole view)
        self.processor.previewLayer.frame = self.view.bounds;
    }
}

//--------------------------------------------------------------------------
- (void)viewDidAppear:(BOOL)animated {
    if (self.processor){
        // setup capture preview layer
        AVCaptureVideoPreviewLayer* previewLayer = self.processor.previewLayer;
        previewLayer.frame = self.view.bounds;
        previewLayer.videoGravity = AVLayerVideoGravityResizeAspectFill;

        if ([previewLayer.connection isVideoOrientationSupported]) {
            previewLayer.connection.videoOrientation = [self interfaceOrientationToVideoOrientation:[UIApplication sharedApplication].statusBarOrientation];
        }

        [self.view.layer insertSublayer:previewLayer below:[[self.view.layer sublayers] objectAtIndex:0]];

        [self.view addSubview:[self buildOverlayView]];
    }
    [self startCapturing];

    [super viewDidAppear:animated];
}

- (AVCaptureVideoOrientation)interfaceOrientationToVideoOrientation:(UIInterfaceOrientation)orientation {
    switch (orientation) {
        case UIInterfaceOrientationPortrait:
            return AVCaptureVideoOrientationPortrait;
        case UIInterfaceOrientationPortraitUpsideDown:
            return AVCaptureVideoOrientationPortraitUpsideDown;
        case UIInterfaceOrientationLandscapeLeft:
            return AVCaptureVideoOrientationLandscapeLeft;
        case UIInterfaceOrientationLandscapeRight:
            return AVCaptureVideoOrientationLandscapeRight;
        default:
            return AVCaptureVideoOrientationPortrait;
   }
}

//--------------------------------------------------------------------------
- (void)startCapturing {
    if (self.processorZXing)
        self.processorZXing.capturing = YES;
    else if (self.processor)
        self.processor.capturing = YES;
}

//--------------------------------------------------------------------------
- (IBAction)shutterButtonPressed {
    self.shutterPressed = YES;
}

//--------------------------------------------------------------------------
- (IBAction)cancelButtonPressed:(id)sender {
    if (self.processorZXing)
        [self.processorZXing performSelector:@selector(barcodeScanCancelled) withObject:nil afterDelay:0];
    else if (self.processor)
        [self.processor performSelector:@selector(barcodeScanCancelled) withObject:nil afterDelay:0];
}

- (IBAction)torchButtonPressed:(id)sender
{
    if (self.processor){
        [self.processor performSelector:@selector(toggleTorch) withObject:nil afterDelay:0];
    }
}
- (void)switchTorchOnOff:(id)sender
{
  if (self.processorZXing) {
    AVCaptureDevice    *dvc = self.processorZXing.inputDevice;
    AVCaptureTorchMode tm = dvc.torchMode == AVCaptureTorchModeOff ? AVCaptureTorchModeOn : AVCaptureTorchModeOff;
    
    if ([dvc isTorchModeSupported:tm])
    {
        [dvc lockForConfiguration:nil];
        [dvc setTorchMode:tm];
        [dvc unlockForConfiguration];
        
        NSString *btnName = tm == AVCaptureTorchModeOn ? @"icons8FlashOff" : @"icons8FlashOn";
        [switchTorchBtn setImage:[self.processorZXing.plugin pluginImageResource:btnName]];
    }
    else
        [switchTorchBtn setEnabled:false];
  }
}

- (IBAction)flipCameraButtonPressed:(id)sender
{
    if (self.processorZXing) {
        [self.processorZXing performSelector:@selector(flipCamera) withObject:nil afterDelay:0];
    } else if (self.processor)
        [self.processor performSelector:@selector(flipCamera) withObject:nil afterDelay:0];
}

//--------------------------------------------------------------------------
- (UIView *)buildOverlayViewFromXib
{
    [[NSBundle mainBundle] loadNibNamed:self.alternateXib owner:self options:NULL];

    if ( self.overlayView == nil )
    {
        NSLog(@"%@", @"An error occurred loading the overlay xib.  It appears that the overlayView outlet is not set.");
        return nil;
    }
    if (self.processor) {
   	    self.overlayView.autoresizesSubviews = YES;
        self.overlayView.autoresizingMask    = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleHeight;
        self.overlayView.opaque              = NO;

	      CGRect bounds = self.view.bounds;
          bounds = CGRectMake(0, 0, bounds.size.width, bounds.size.height);

	      [self.overlayView setFrame:bounds];
    }

    return self.overlayView;
}

//--------------------------------------------------------------------------
- (UIView*)buildOverlayView {

    if ( nil != self.alternateXib )
    {
        return [self buildOverlayViewFromXib];
    }
    CGRect bounds;
    if (self.processorZXing)
        bounds = self.view.bounds;
    else
        bounds = self.view.frame;
    bounds = CGRectMake(0, 0, bounds.size.width, bounds.size.height);

    UIView* overlayView = [[UIView alloc] initWithFrame:bounds];
    overlayView.autoresizesSubviews = YES;
    overlayView.autoresizingMask    = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleHeight;
    overlayView.opaque              = NO;

    self.toolbar = [[UIToolbar alloc] init];
    UIToolbar* toolbar = self.toolbar;
    CDVPlugin* plugin;

    if (self.processorZXing) {
        toolbar.autoresizingMask = UIViewAutoresizingFlexibleWidth | UIViewAutoresizingFlexibleTopMargin;
        if (self.processorZXing.hasToolbarBlack)
        {
            [toolbar setBarStyle:UIBarStyleBlack];
            [toolbar setTintColor:[UIColor whiteColor]];
        }
        if (self.processorZXing.hasToolbarTranslucent)
            [toolbar setAlpha:0.7];
        plugin = self.processorZXing.plugin;
    } else if (self.processor) {
        toolbar.autoresizingMask = UIViewAutoresizingFlexibleWidth;
        plugin = self.processor.plugin;
    }
    
    id cancelButton = [[UIBarButtonItem alloc]
                       initWithBarButtonSystemItem:UIBarButtonSystemItemCancel
                       target:(id)self
                       action:@selector(cancelButtonPressed:)
                       ];


    id flexSpace = [[UIBarButtonItem alloc]
                    initWithBarButtonSystemItem:UIBarButtonSystemItemFlexibleSpace
                    target:nil
                    action:nil
                    ];

    id flipCamera = [[UIBarButtonItem alloc]
                       initWithBarButtonSystemItem:UIBarButtonSystemItemCamera
                       target:(id)self
                       action:@selector(flipCameraButtonPressed:)
                       ];

    NSMutableArray *items;

#if USE_SHUTTER
    id shutterButton = [[UIBarButtonItem alloc]
                        initWithBarButtonSystemItem:UIBarButtonSystemItemCamera
                        target:(id)self
                        action:@selector(shutterButtonPressed)
                        ];

    if (self.processor && self.processor.isShowFlipCameraButton) {
      items = [NSMutableArray arrayWithObjects:flexSpace, cancelButton, flexSpace, flipCamera, shutterButton, nil];
    } else {
      items = [NSMutableArray arrayWithObjects:flexSpace, cancelButton, flexSpace, shutterButton, nil];
    }
#else
    if (self.processor && self.processor.isShowFlipCameraButton) {
      items = [@[flexSpace, cancelButton, flexSpace, flipCamera] mutableCopy];
    } else {
      items = [@[flexSpace, cancelButton, flexSpace] mutableCopy];
    }
#endif

    if (self.processorZXing) {
      if (self.processorZXing.inputDevice.hasTorch)
      {
          switchTorchBtn = [[UIBarButtonItem alloc]
                          initWithImage:[plugin pluginImageResource:@"icons8FlashOn"]
                          style:UIBarButtonItemStylePlain
                          target:(id)self
                          action:@selector(switchTorchOnOff:)
                          ];
        
          toolbar.items = [NSArray arrayWithObjects:cancelButton, flexSpace, switchTorchBtn, flexSpace, flipCamera,
#if USE_SHUTTER
                         flexSpace, shutterButton,
#endif
                         nil];
          [switchTorchBtn setEnabled:self.processorZXing.inputDevice.torchAvailable];
      }
      else
          toolbar.items = [NSArray arrayWithObjects:cancelButton, flexSpace, flipCamera,
#if USE_SHUTTER
                           flexSpace, shutterButton,
#endif
                         nil];
    
        bounds = overlayView.bounds;
    
        [toolbar sizeToFit];
        CGFloat toolbarHeight  = [toolbar frame].size.height;
        CGFloat rootViewHeight = CGRectGetHeight(bounds);
        CGFloat rootViewWidth  = CGRectGetWidth(bounds);
        CGRect  rectArea       = CGRectMake(0, rootViewHeight - toolbarHeight, rootViewWidth, toolbarHeight);
        [toolbar setFrame:rectArea];
    
        [overlayView addSubview: toolbar];
    
        [overlayView addSubview: [self buildReticleView:bounds]];
    } else if (self.processor) {
        if (self.processor.isShowTorchButton && !self.processor.isFrontCamera) {
          AVCaptureDevice *device = [AVCaptureDevice defaultDeviceWithMediaType:AVMediaTypeVideo];
          if ([device hasTorch] && [device hasFlash]) {
            NSURL *bundleURL = [[NSBundle mainBundle] URLForResource:@"CDVBarcodeScanner" withExtension:@"bundle"];
            NSBundle *bundle = [NSBundle bundleWithURL:bundleURL];
            NSString *imagePath = [bundle pathForResource:@"torch" ofType:@"png"];
            UIImage *image = [UIImage imageWithContentsOfFile:imagePath];

            id torchButton = [[UIBarButtonItem alloc]
                           initWithImage:image
                                   style:UIBarButtonItemStylePlain
                                  target:(id)self
                                  action:@selector(torchButtonPressed:)
                           ];

            [items insertObject:torchButton atIndex:0];
          }
        }
        self.toolbar.items = items;
        [overlayView addSubview: self.toolbar];

        UIImage* reticleImage = [self buildReticleImage];
        self.reticleView = [[UIImageView alloc] initWithImage:reticleImage];

        self.reticleView.opaque           = NO;
        self.reticleView.contentMode      = UIViewContentModeScaleAspectFit;
        self.reticleView.autoresizingMask = (UIViewAutoresizing) (0
            | UIViewAutoresizingFlexibleLeftMargin
            | UIViewAutoresizingFlexibleRightMargin
            | UIViewAutoresizingFlexibleTopMargin
            | UIViewAutoresizingFlexibleBottomMargin)
        ;

        [overlayView addSubview: self.reticleView];
        [self resizeElements];
    }
    return overlayView;
}

- (UIView *)buildReticleView:(CGRect)bounds {
    UIImage* reticleImage   = [self buildReticleImage];
    UIView*  reticleView    = [[UIImageView alloc] initWithImage: reticleImage];
    CGFloat  rootViewHeight = CGRectGetHeight(bounds)
    ,        rootViewWidth  = CGRectGetWidth(bounds);
    CGFloat  minAxis        = MIN(rootViewHeight, rootViewWidth);
    
    CGRect  rectArea        = CGRectMake(
                                         0,
                                         0.5 * (rootViewHeight - minAxis),
                                         rootViewWidth,
                                         minAxis
                                         );
    
    [reticleView setFrame:rectArea];
    
    reticleView.opaque           = NO;
    reticleView.contentMode      = UIViewContentModeScaleAspectFit;
    reticleView.autoresizingMask = 0
    | UIViewAutoresizingFlexibleLeftMargin
    | UIViewAutoresizingFlexibleRightMargin
    | UIViewAutoresizingFlexibleTopMargin
    | UIViewAutoresizingFlexibleBottomMargin
    ;
    
    return reticleView;
}

//--------------------------------------------------------------------------

#define RETICLE_SIZE    500.0f
#define RETICLE_WIDTH    10.0f
#define RETICLE_OFFSET   60.0f
#define RETICLE_ALPHA     0.4f

//-------------------------------------------------------------------------
// builds the green box and red line
//-------------------------------------------------------------------------
- (UIImage*)buildReticleImage {
    UIImage* result;
    CGFloat widthFactor = UIInterfaceOrientationIsLandscape([[UIApplication sharedApplication] statusBarOrientation]) ? 2 : 1;
    if (self.processorZXing)
        UIGraphicsBeginImageContext(CGSizeMake(widthFactor*RETICLE_SIZE, RETICLE_SIZE));
    else
        UIGraphicsBeginImageContext(CGSizeMake(RETICLE_SIZE, RETICLE_SIZE));
    CGContextRef context = UIGraphicsGetCurrentContext();

    if (self.processorZXing && self.processorZXing.is1D) {
        UIColor* color = [UIColor colorWithRed:1.0 green:0.0 blue:0.0 alpha:RETICLE_ALPHA];
        CGContextSetStrokeColorWithColor(context, color.CGColor);
        CGContextSetLineWidth(context, RETICLE_WIDTH);
        CGContextBeginPath(context);
        CGFloat lineOffset = RETICLE_OFFSET+(0.5*RETICLE_WIDTH);
        CGContextMoveToPoint(context, lineOffset, RETICLE_SIZE/2);
        CGContextAddLineToPoint(context, widthFactor*RETICLE_SIZE-lineOffset, 0.5*RETICLE_SIZE);
        CGContextStrokePath(context);
    } else if (self.processor && self.processor.is1D) {
        UIColor* color = [UIColor colorWithRed:1.0 green:0.0 blue:0.0 alpha:RETICLE_ALPHA];
        CGContextSetStrokeColorWithColor(context, color.CGColor);
        CGContextSetLineWidth(context, RETICLE_WIDTH);
        CGContextBeginPath(context);
        CGFloat lineOffset = (CGFloat) (RETICLE_OFFSET+(0.5*RETICLE_WIDTH));
        CGContextMoveToPoint(context, lineOffset, RETICLE_SIZE/2);
        CGContextAddLineToPoint(context, RETICLE_SIZE-lineOffset, (CGFloat) (0.5*RETICLE_SIZE));
        CGContextStrokePath(context);
    }

    if (self.processorZXing && self.processorZXing.is2D) {
        UIColor* color = [UIColor colorWithRed:0.0 green:1.0 blue:0.0 alpha:RETICLE_ALPHA];
        CGContextSetStrokeColorWithColor(context, color.CGColor);
        CGContextSetLineWidth(context, RETICLE_WIDTH);
        CGContextStrokeRect(context,
                            CGRectMake(
                                       RETICLE_OFFSET,
                                       RETICLE_OFFSET,
                                       widthFactor*RETICLE_SIZE-2*RETICLE_OFFSET,
                                       RETICLE_SIZE-2*RETICLE_OFFSET
                                       )
                            );
    } else if (self.processor && self.processor.is2D) {
        UIColor* color = [UIColor colorWithRed:0.0 green:1.0 blue:0.0 alpha:RETICLE_ALPHA];
        CGContextSetStrokeColorWithColor(context, color.CGColor);
        CGContextSetLineWidth(context, RETICLE_WIDTH);
        CGContextStrokeRect(context,
                            CGRectMake(
                                       RETICLE_OFFSET,
                                       RETICLE_OFFSET,
                                       RETICLE_SIZE-2*RETICLE_OFFSET,
                                       RETICLE_SIZE-2*RETICLE_OFFSET
                                       )
                            );
    }

    result = UIGraphicsGetImageFromCurrentImageContext();
    UIGraphicsEndImageContext();
    return result;
}

#pragma mark CDVBarcodeScannerOrientationDelegate

- (BOOL)shouldAutorotate
{
    if ((self.orientationDelegate != nil) && [self.orientationDelegate respondsToSelector:@selector(shouldAutorotate)]) {
        return [self.orientationDelegate shouldAutorotate];
    }
    
    return YES;
}

- (UIInterfaceOrientation)preferredInterfaceOrientationForPresentation
{
    return [[UIApplication sharedApplication] statusBarOrientation];
}

- (NSUInteger)supportedInterfaceOrientations
{
    return UIInterfaceOrientationMaskAll;
}

- (BOOL)shouldAutorotateToInterfaceOrientation:(UIInterfaceOrientation)interfaceOrientation
{
    if ((self.orientationDelegate != nil) && [self.orientationDelegate respondsToSelector:@selector(shouldAutorotateToInterfaceOrientation:)]) {
        return [self.orientationDelegate shouldAutorotateToInterfaceOrientation:interfaceOrientation];
    }

    return YES;
}

- (void) willAnimateRotationToInterfaceOrientation:(UIInterfaceOrientation)orientation duration:(NSTimeInterval)duration
{
    [UIView setAnimationsEnabled:NO];
    AVCaptureVideoPreviewLayer* previewLayer = nil;
    if (self.processorZXing)
        previewLayer = self.processorZXing.previewLayer;
    else if (self.processor)
        previewLayer = self.processor.previewLayer;
    previewLayer.frame = self.view.bounds;

    if (orientation == UIInterfaceOrientationLandscapeLeft) {
        [previewLayer setOrientation:AVCaptureVideoOrientationLandscapeLeft];
    } else if (orientation == UIInterfaceOrientationLandscapeRight) {
        [previewLayer setOrientation:AVCaptureVideoOrientationLandscapeRight];
    } else if (orientation == UIInterfaceOrientationPortrait) {
        [previewLayer setOrientation:AVCaptureVideoOrientationPortrait];
    } else if (orientation == UIInterfaceOrientationPortraitUpsideDown) {
        [previewLayer setOrientation:AVCaptureVideoOrientationPortraitUpsideDown];
    }

    previewLayer.videoGravity = AVLayerVideoGravityResizeAspectFill;

    [self resizeElements];
    [UIView setAnimationsEnabled:YES];
}

-(void) resizeElements {
    CGRect bounds = self.view.bounds;
    if (@available(iOS 11.0, *)) {
        bounds = CGRectMake(bounds.origin.x, bounds.origin.y, bounds.size.width, self.view.safeAreaLayoutGuide.layoutFrame.size.height+self.view.safeAreaLayoutGuide.layoutFrame.origin.y);
    }

    [self.toolbar sizeToFit];
    CGFloat toolbarHeight  = [self.toolbar frame].size.height;
    CGFloat rootViewHeight = CGRectGetHeight(bounds);
    CGFloat rootViewWidth  = CGRectGetWidth(bounds);
    CGRect  rectArea       = CGRectMake(0, rootViewHeight - toolbarHeight, rootViewWidth, toolbarHeight);
    [self.toolbar setFrame:rectArea];

    CGFloat minAxis = MIN(rootViewHeight, rootViewWidth);

    rectArea = CGRectMake(
                          (CGFloat) (0.5 * (rootViewWidth  - minAxis)),
                          (CGFloat) (0.5 * (rootViewHeight - minAxis)),
                          minAxis,
                          minAxis
                          );

    [self.reticleView setFrame:rectArea];
    self.reticleView.center = CGPointMake(self.view.center.x, self.view.center.y-self.toolbar.frame.size.height/2);
}

@end

