import asyncio
import logging
import json
import aiohttp
import os
import random
import re
from datetime import datetime, timedelta
from telegram import (Update, InlineKeyboardButton, InlineKeyboardMarkup,
                       InputMediaPhoto, InputMediaVideo, InputMediaAnimation, InputMediaDocument)
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes, MessageHandler, filters
from telegram.constants import ParseMode
from telegram.error import NetworkError, TimedOut, RetryAfter
import time
import tempfile
from collections import Counter, deque
import numpy as np
import pickle
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
import hashlib
from pathlib import Path
from pymongo import MongoClient

# Pyrogram for user account (premium emoji support)
from pyrogram import Client
from pyrogram.errors import FloodWait, PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant
from pyrogram.enums import ParseMode as PyrogramParseMode
from pyrogram.types import InputMediaPhoto as PyrogramInputMediaPhoto
from pyrogram.types import InputMediaVideo as PyrogramInputMediaVideo
from pyrogram.types import InputMediaDocument as PyrogramInputMediaDocument
from pyrogram.types import InputMediaAnimation as PyrogramInputMediaAnimation

# Configure logging
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logging.getLogger('httpx').setLevel(logging.WARNING)
logging.getLogger('apscheduler').setLevel(logging.WARNING)
logging.getLogger('telegram').setLevel(logging.WARNING)
logging.getLogger('pyrogram').setLevel(logging.WARNING)

class WinGoBotEnhanced:
    def __init__(self, bot_token, api_id=None, api_hash=None, phone=None):
        self.bot_token = bot_token
        self.config_file = 'wingo_config.json'
        self.templates_file = 'templates.json'
        self.emoji_config_file = 'emoji_config.json'
        self.ai_model_file = 'ai_pattern_model.pkl'
        self.pattern_history_file = 'pattern_history.json'
        self.custom_messages_file = 'custom_messages.json'

        # MongoDB storage
        self.bot_name = Path(__file__).stem
        self.mongo_uri = os.getenv('MONGO_URI', 'mongodb+srv://avinash:avinash12@cluster0.wnwd1fv.mongodb.net/?appName=Cluster0')
        self.mongo_db_name = os.getenv('MONGO_DB', 'sanjay_bots')
        self.mongo_client = None
        self.mongo_db = None
        self._init_mongo()

        # Pyrogram User Account
        self.api_id = api_id
        self.api_hash = api_hash
        self.phone = phone
        self.user_app = None
        self.user_client_initialized = False
        self.user_client_lock = asyncio.Lock()
        self.use_user_account = bool(api_id and api_hash and phone)
        
        self.username_to_id = {}
        self.id_to_username = {}
        self.resolved_channels = set()
        self.failed_channels = set()
        self.resolution_in_progress = False
        self.user_client_connected = False
        self.user_client_keepalive_task = None
        
        self.emoji_placeholders = {}

        # Session tracking
        self.current_session = ""
        self.last_session_check = None
        self.session_ended = True
        self.waiting_for_win = False
        self.last_prediction_was_loss = False
        self.in_break_period = False
        self.night_mode = False
        self.morning_message_sent = False
        self.night_message_sent = False
        
        # Channel time windows
        self.default_time_windows = {
            'default': [
                {'start': '10:00', 'end': '11:00', 'name': 'Morning Session'},
                {'start': '13:00', 'end': '14:00', 'name': 'Afternoon Session'},
                {'start': '17:00', 'end': '18:00', 'name': 'Evening Session'},
                {'start': '20:00', 'end': '21:00', 'name': 'Night Session'}
            ]
        }
        
        self.channel_time_windows = {}
        self.operational_hours_start = 8
        self.operational_hours_end = 0

        # Custom Break Duration
        self.custom_break_duration = 60

        # Channel management
        self.active_channels = []
        self.channel_configs = {}
        self.channel_prediction_status = {}
        self.channel_subscriptions = {}

        # Prediction message tracking
        self.prediction_message_ids = {}
        self.cycle_prediction_ids = {}
        self.max_loss_predictions_keep = 3

        # Break control
        self.pending_break = False
        self.pending_break_next_session = None

        # Track last sent message
        self.last_sent_period = None
        self.last_prediction_time = None

        # Single prediction mode
        self.current_prediction_period = None
        self.current_prediction_choice = None
        self.waiting_for_result = False
        self.break_message_sent = False
        self.last_result_was_win = False
        self.break_start_time = None
        self.session_start_sent = False

        # Prediction tracking
        self.last_processed_period = None
        self.predictions = {}
        self.user_state = {}
        self.session_predictions = []

        # Advanced prediction tracking
        self.consecutive_losses = 0
        self.consecutive_wins = 0
        self.prediction_history = []
        self.last_10_results = []
        self.pattern_memory = deque(maxlen=1000)
        self.number_memory = deque(maxlen=1000)
        self.recent_results = deque(maxlen=200)
        self.recent_numbers = deque(maxlen=200)

        # Advanced loss prevention
        self.session_wins = 0
        self.session_losses = 0
        self.total_wins = 0
        self.total_losses = 0
        self.safety_mode = False
        self.recovery_mode = False
        self.ultra_safe_mode = False
        self.last_5_predictions = []

        # AI PATTERN RECOGNITION SYSTEM
        self.ai_model = None
        self.scaler = None
        self.pattern_history = []
        self.successful_patterns = []
        self.failed_patterns = []
        self.learning_rate = 0.1
        self.pattern_database = {}
        self.ai_confidence_threshold = 0.75
        self.min_training_samples = 100
        
        self.pattern_window_size = 20
        self.feature_count = 15
        self.ai_prediction_history = deque(maxlen=200)
        
        self.pattern_weights = {
            'streak_breaker': 0.25,
            'balance_correction': 0.35,
            'gap_filling': 0.25,
            'number_pattern': 0.10,
            'alternating': 0.05,
            'random_walk': 0.15,
            'history_trend': 0.20,
            'ai_pattern': 0.45
        }

        self.learning_history = deque(maxlen=1000)
        self.last_winning_strategy = None
        self.strategy_success_count = {}
        self.recent_patterns = deque(maxlen=100)
        
        self.big_small_history = deque(maxlen=500)
        self.number_distribution = {i: 0 for i in range(10)}
        self.prediction_streak_threshold = 3
        self.last_actual_results = deque(maxlen=100)
        
        self.ai_correct_predictions = 0
        self.ai_total_predictions = 0
        self.ai_accuracy = 0.0
        self.ai_learning_cycles = 0
        self.last_ai_pattern_used = None
        
        self.pattern_types = {
            'alternating': 0,
            'streak': 0,
            'zigzag': 0,
            'cluster': 0,
            'random': 0,
            'cycle': 0
        }

        self.event_media = {}
        self.custom_messages = {}
        
        self.message_types = {
            'session_start': 'Session Start',
            'break': 'Break',
            'good_morning': 'Good Morning',
            'good_night': 'Good Night',
            'win': 'Win Result',
            'loss': 'Loss Result',
            'prediction': 'Prediction',
            'custom': 'Custom'
        }

        self.default_templates = {
            "prediction_header": "{crown} 𝐁𝐃𝐆 𝐖𝐈𝐍 𝐖𝐈𝐍𝐆𝐎 𝐎𝐅𝐅𝐈𝐂𝐈𝐀𝐋 {crown}\n   ——————————————\n        {sparkles} 𝟭 𝗠𝗜𝗡  𝗪𝗜𝐍𝐆𝐎  {sparkles}\n    —————————————",
            "session_line": "      {check} 𝐒𝐄𝐒𝐒𝐈𝐎𝐍: {session}",
            "maintain_level": "    —————————————\n    {chart}  MAINTAIN 8 LEVEL  {chart}\n    —————————————",
            "prediction_footer": "\n\n\n\n\n\n    {link} 𝐑𝐞𝐠𝐢𝐬𝐭𝐞𝐫 𝐋𝐢𝐧𝐤: \n    {register_link}\n    \n    —————————————\n    \n    {promo_text}\n    \n    —————————————",
            "good_morning": "{sun} 𝐆𝐎𝐎𝐃 𝐌𝐎𝐑𝐍𝐈𝐍𝐆 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! {sun}\n\n{sparkles} A new day of winning begins!\n{lightning} Starting at 8:00 AM sharp!\n{money} Let's make today profitable!\n\n{coffee} Have your coffee ready...\n{rocket} Ultra-smart predictions starting soon!",
            "good_night": "{moon} 𝐆𝐎𝐎𝐃 𝐍𝐈𝐆𝐇𝐓 𝐖𝐈𝐍𝐍𝐄𝐑𝐒! {moon}\n\n{sleep} Going to sleep now...\n{clock} Will be back tomorrow at 6:00 AM\n\n{moon} Sweet dreams winners!\n{reload} See you tomorrow for more wins!",
            "break_message": "{break_icon} 𝐁𝐑𝐄𝐀𝐊 𝐓𝐈𝐌𝐄 {break_icon}\n\n🌀 {break_duration} Minutes Break\n{clock} Next Session: {next_session}\n\n{sleep} Taking a short break...\n{reload} Back with even smarter predictions!\n\nDon't miss this opportunity!\n{target} Next session starts in {break_duration} minutes...",
            "new_session": "{reload} 𝐍𝐄𝐖 𝐒𝐄𝐒𝐒𝐈𝐎𝐍 𝐒𝐓𝐀𝐑𝐓𝐄𝐃 {reload}\n\n{crown} 𝐁𝐃𝐆 𝐖𝐈𝐍 𝐖𝐈𝐍𝐆𝐎 𝐎𝐅𝐅𝐈𝐂𝐈𝐀𝐋 {crown}\n   ——————————————\n        {sparkles} 𝟭 𝗠𝗜𝗡  𝗪𝗜𝐍𝐆𝐎  {sparkles}\n    —————————————\n      {check} 𝐒𝐄𝐒𝐒𝐈𝐎𝐍: {session}\n    —————————————\n\n    —————————————\n\n    {rocket} Session Started! Ultra-accurate predictions incoming...",
            "single_prediction": "{crown} 𝗝𝗢𝗜𝗡 𝗣𝗥𝗢𝗠𝗢𝗧𝗘𝗥 𝗧𝗘𝗔𝗠 {crown}\n\n{link} {register_link}\n\n{fire} 𝗪𝗜𝗡𝗚𝗢 ❶ 𝗠𝗜𝗡𝗨𝗧𝗘 {fire}\n\n{period}",
            "session_end": "{moon} 𝐒𝐄𝐒𝐒𝐈𝐎𝐍 𝐄𝐍𝐃𝐄𝐃 {moon}\n\n{sleep} Break time!\n{clock} Next session: {next_session}\n\n{trophy} Today's stats:\nWins: {wins} | Losses: {losses}\nWin Rate: {win_rate:.1f}%"
        }

        self.custom_break_messages = {}
        self.custom_break_schedules = {}
        self.media_group_messages = {}
        self.scheduled_tasks = {}
        self.sent_custom_messages_in_break = {}
        
        self.initialize_configs()
        self.initialize_ai_model()
        self._init_channel_time_windows()

    def _init_channel_time_windows(self):
        """Initialize default time windows for channels based on channel order"""
        self.channel_time_windows = {}

    def _get_default_windows_for_channel(self, channel_index):
        """Get default time windows based on channel index"""
        if channel_index == 0:
            return [
                {'start': '10:00', 'end': '11:00', 'name': 'Morning Session'},
                {'start': '13:00', 'end': '14:00', 'name': 'Afternoon Session'},
                {'start': '17:00', 'end': '18:00', 'name': 'Evening Session'},
                {'start': '20:00', 'end': '21:00', 'name': 'Night Session'}
            ]
        else:
            return [
                {'start': '09:30', 'end': '10:30', 'name': 'Morning Session'},
                {'start': '13:30', 'end': '14:30', 'name': 'Afternoon Session'},
                {'start': '16:30', 'end': '17:30', 'name': 'Evening Session'},
                {'start': '20:30', 'end': '21:30', 'name': 'Night Session'}
            ]

    def _init_mongo(self):
        """Initialize MongoDB connection."""
        try:
            self.mongo_client = MongoClient(self.mongo_uri, serverSelectionTimeoutMS=8000)
            self.mongo_db = self.mongo_client[self.mongo_db_name]
            self.mongo_client.admin.command('ping')
            logging.info(f"✅ MongoDB connected for {self.bot_name}")
        except Exception as e:
            logging.error(f"❌ MongoDB connection failed for {self.bot_name}: {e}")
            self.mongo_client = None
            self.mongo_db = None

    def _mongo_get_doc(self, doc_type):
        if self.mongo_db is None:
            return None
        try:
            return self.mongo_db.bot_data.find_one({'bot_name': self.bot_name, 'type': doc_type})
        except Exception as e:
            logging.error(f"❌ Mongo read failed ({doc_type}): {e}")
            return None

    def _mongo_upsert_doc(self, doc_type, data):
        if self.mongo_db is None:
            return False
        try:
            self.mongo_db.bot_data.update_one(
                {'bot_name': self.bot_name, 'type': doc_type},
                {'$set': {
                    'bot_name': self.bot_name,
                    'type': doc_type,
                    'data': data,
                    'updated_at': datetime.utcnow()
                }},
                upsert=True
            )
            return True
        except Exception as e:
            logging.error(f"❌ Mongo write failed ({doc_type}): {e}")
            return False

    async def initialize_user_client(self):
        """Initialize Pyrogram user client"""
        if not self.use_user_account:
            logging.warning("User account not configured. Using regular emojis.")
            return False

        async with self.user_client_lock:
            if self.user_client_initialized and self.user_app and self.user_client_connected:
                return True

            try:
                session_name = str((Path(__file__).resolve().parent / "user_session_sanjay").resolve())
                
                self.user_app = Client(
                    session_name,
                    api_id=self.api_id,
                    api_hash=self.api_hash,
                    phone_number=self.phone,
                    in_memory=False,
                    sleep_threshold=30,
                    no_updates=True
                )

                await self.user_app.start()
                self.user_client_initialized = True
                self.user_client_connected = True
                
                me = await self.user_app.get_me()
                logging.info(f"✅ User account connected: {me.first_name} (ID: {me.id})")
                
                if hasattr(me, 'is_premium') and me.is_premium:
                    logging.info("✅ Premium account detected! Premium emojis will work.")

                self.user_client_keepalive_task = asyncio.create_task(self._keep_user_client_alive())
                logging.info("✅ User client keepalive task started")

                await self.resolve_all_channels()
                
                return True

            except Exception as e:
                logging.error(f"❌ Failed to initialize user account: {e}")
                self.user_client_connected = False
                self.user_client_initialized = False
                return False

    async def _keep_user_client_alive(self):
        """Keep user client alive with periodic pings"""
        try:
            while True:
                await asyncio.sleep(30)
                if self.user_app and self.user_client_connected:
                    try:
                        await self.user_app.get_me()
                        logging.debug("✅ User client ping successful")
                    except Exception as e:
                        logging.warning(f"⚠️ User client ping failed: {e}")
                        self.user_client_connected = False
                        await self._reconnect_user_client()
                else:
                    await self._reconnect_user_client()
        except asyncio.CancelledError:
            logging.info("🛑 User client keepalive stopped")
        except Exception as e:
            logging.error(f"❌ Keepalive error: {e}")

    async def _reconnect_user_client(self):
        """Reconnect user client if disconnected"""
        try:
            if self.user_app:
                try:
                    await self.user_app.stop()
                except:
                    pass
                await asyncio.sleep(2)
                await self.user_app.start()
                self.user_client_connected = True
                logging.info("✅ User client reconnected")
        except Exception as e:
            logging.error(f"❌ Failed to reconnect user client: {e}")
            self.user_client_connected = False

    async def ensure_user_client_connected(self):
        return self.user_client_connected and self.user_app is not None

    async def resolve_all_channels(self):
        """Resolve all channels"""
        if not self.user_app or not self.active_channels:
            return
        
        if self.resolution_in_progress:
            return
        
        self.resolution_in_progress = True
        logging.info("🔍 Resolving all channels...")
        
        self.username_to_id.clear()
        self.id_to_username.clear()
        self.resolved_channels.clear()
        
        for channel in self.active_channels:
            try:
                channel_str = str(channel).strip()
                
                if channel_str in self.failed_channels:
                    continue
                
                try:
                    if channel_str.startswith('@'):
                        chat = await self.user_app.get_chat(channel_str)
                        self.username_to_id[channel_str] = chat.id
                        self.id_to_username[str(chat.id)] = channel_str
                        self.resolved_channels.add(chat.id)
                        self.resolved_channels.add(channel_str)
                        logging.info(f"✅ Resolved {channel_str} -> {chat.id} (Title: {chat.title})")
                    
                    elif channel_str.lstrip('-').isdigit():
                        chat_id = int(channel_str)
                        chat = await self.user_app.get_chat(chat_id)
                        
                        self.username_to_id[channel_str] = chat_id
                        self.id_to_username[str(chat_id)] = channel_str
                        self.resolved_channels.add(chat_id)
                        self.resolved_channels.add(channel_str)
                        
                        if hasattr(chat, 'username') and chat.username:
                            username = f"@{chat.username}"
                            self.username_to_id[username] = chat_id
                            self.id_to_username[str(chat_id)] = username
                            self.resolved_channels.add(username)
                        
                        logging.info(f"✅ Resolved {channel_str} -> {chat_id} (Title: {chat.title})")
                    
                    else:
                        logging.warning(f"⚠️ Invalid channel format: {channel_str}")
                        self.failed_channels.add(channel_str)
                        
                except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
                    logging.error(f"❌ Cannot access channel {channel_str}: {e}")
                    self.failed_channels.add(channel_str)
                except FloodWait as e:
                    logging.warning(f"⚠️ FloodWait: Waiting {e.value}s")
                    await asyncio.sleep(e.value)
                    
            except Exception as e:
                logging.error(f"❌ Failed to resolve {channel}: {e}")
                self.failed_channels.add(str(channel))
        
        logging.info(f"✅ Resolved {len(self.resolved_channels)} channel references")
        self.resolution_in_progress = False

    async def get_chat_id(self, channel_identifier):
        if not self.user_app:
            return None
        
        identifier = str(channel_identifier).strip()
        
        if identifier in self.username_to_id:
            return self.username_to_id[identifier]
        
        if identifier.lstrip('-').isdigit():
            chat_id = int(identifier)
            if chat_id in self.id_to_username:
                return chat_id
        
        try:
            if identifier.startswith('@'):
                chat = await self.user_app.get_chat(identifier)
                self.username_to_id[identifier] = chat.id
                self.id_to_username[str(chat.id)] = identifier
                return chat.id
            elif identifier.lstrip('-').isdigit():
                chat_id = int(identifier)
                chat = await self.user_app.get_chat(chat_id)
                self.username_to_id[identifier] = chat_id
                self.id_to_username[str(chat_id)] = identifier
                return chat_id
        except Exception as e:
            logging.error(f"❌ Failed to resolve {identifier}: {e}")
            self.failed_channels.add(identifier)
        
        return None

    def get_file_extension(self, file_name):
        if not file_name:
            return ''
        
        name = str(file_name).lower()
        ext = name.split('.')[-1] if '.' in name else ''
        return f".{ext}" if ext else ''

    def detect_media_type_from_file(self, file_name, mime_type=None):
        if not file_name and not mime_type:
            return 'document', 'document'
        
        file_name = str(file_name).lower() if file_name else ''
        mime_type = str(mime_type).lower() if mime_type else ''
        
        if file_name.endswith('.webp') or file_name.endswith('.tgs'):
            return 'sticker', 'sticker'
        
        if mime_type in ['image/webp', 'application/x-tgsticker']:
            return 'sticker', 'sticker'
        
        video_extensions = ['.mp4', '.mkv', '.mov', '.webm', '.avi', '.gif']
        if any(file_name.endswith(ext) for ext in video_extensions) or mime_type.startswith('video/'):
            return 'video', 'video'
        
        image_extensions = ['.jpg', '.jpeg', '.png', '.bmp', '.gif']
        if any(file_name.endswith(ext) for ext in image_extensions) or mime_type.startswith('image/'):
            return 'photo', 'photo'
        
        if file_name.endswith('.gif') or mime_type == 'image/gif':
            return 'animation', 'animation'
        
        return 'document', 'document'

    async def fetch_live_data(self):
        """Fetch live data from working API"""
        url = "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json"
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
            'Accept': 'application/json, text/plain, */*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Origin': 'https://draw.ar-lottery01.com',
            'Referer': 'https://draw.ar-lottery01.com/',
            'Accept-Encoding': 'gzip, deflate, br',
            'Connection': 'keep-alive'
        }
        
        max_retries = 3
        for attempt in range(max_retries):
            try:
                timeout = aiohttp.ClientTimeout(total=15, connect=10)
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    async with session.get(url, headers=headers) as response:
                        if response.status != 200:
                            logging.error(f"API returned status code: {response.status}")
                            if attempt < max_retries - 1:
                                await asyncio.sleep(2 ** attempt)
                                continue
                            return None
                        
                        try:
                            data = await response.json()
                        except:
                            text = await response.text()
                            try:
                                data = json.loads(text)
                            except:
                                logging.error("Failed to parse API response as JSON")
                                if attempt < max_retries - 1:
                                    await asyncio.sleep(2 ** attempt)
                                    continue
                                return None
                        
                        if data.get('data') and data['data'].get('list'):
                            data_list = data['data']['list']
                            formatted_data = []
                            
                            for item in data_list:
                                try:
                                    number_str = str(item.get('number', '0'))
                                    number_clean = ''.join(filter(str.isdigit, number_str))
                                    number = int(number_clean[0]) if number_clean else 0
                                    
                                    formatted_item = {
                                        'issueNumber': item.get('issueNumber'),
                                        'number': number,
                                        'color': self.get_color(number),
                                        'big_small': self.get_big_small(number),
                                        'premium': item.get('premium', ''),
                                        'sum': item.get('sum', '')
                                    }
                                    formatted_data.append(formatted_item)
                                except Exception as e:
                                    continue
                            
                            for item in formatted_data[:20]:
                                self.pattern_memory.append({
                                    'result': item['big_small'],
                                    'number': item['number'],
                                    'timestamp': datetime.now()
                                })
                                self.number_memory.append(item['number'])
                                self.recent_results.append(item['big_small'])
                                self.recent_numbers.append(item['number'])
                                self.big_small_history.append(item['big_small'])
                                self.number_distribution[item['number']] += 1
                                self.last_actual_results.append(item['big_small'])
                            
                            return formatted_data
                        
                        return None
                        
            except asyncio.TimeoutError:
                logging.warning(f"API timeout on attempt {attempt + 1}/{max_retries}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                else:
                    return None
                    
            except Exception as e:
                logging.error(f"API error on attempt {attempt + 1}/{max_retries}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                else:
                    return None
        
        return None

    def get_big_small(self, num):
        return 'SMALL' if num <= 4 else 'BIG'

    def get_color(self, num):
        if num == 0:
            return 'GREEN'
        elif num in [1, 3, 5, 7, 9]:
            return 'RED'
        else:
            return 'VIOLET'

    def get_next_period(self, current_period):
        try:
            return str(int(current_period) + 1)
        except:
            import re
            numbers = re.findall(r'\d+', current_period)
            return str(int(numbers[-1]) + 1) if numbers else "000001"

    def set_channel_time_windows(self, channel_id, windows):
        """Set time windows for a channel"""
        self.channel_time_windows[channel_id] = windows
        self.save_config()
        logging.info(f"✅ Set {len(windows)} time windows for {channel_id}")
        
    def get_channel_time_windows(self, channel_id):
        """Get time windows for a channel"""
        if channel_id in self.channel_time_windows:
            return self.channel_time_windows[channel_id]
        
        try:
            channel_index = self.active_channels.index(channel_id) if channel_id in self.active_channels else 0
            windows = self._get_default_windows_for_channel(channel_index)
            self.channel_time_windows[channel_id] = windows
            return windows
        except:
            return self._get_default_windows_for_channel(0)
    
    def is_channel_in_time_window(self, channel_id, dt=None):
        """Check if channel is currently in an active time window"""
        if dt is None:
            dt = self.get_ist_now()
        
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        
        for window in windows:
            start = window['start']
            end = window['end']
            
            if start <= current_time < end:
                return True
        
        return False
    
    def get_minutes_until_session_start(self, channel_id, dt=None):
        """Get minutes until next session start for channel"""
        if dt is None:
            dt = self.get_ist_now()
        
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        
        sorted_windows = sorted(windows, key=lambda w: w['start'])
        
        for window in sorted_windows:
            if window['start'] > current_time:
                start_hour, start_min = map(int, window['start'].split(':'))
                current_hour = dt.hour
                current_min = dt.minute
                
                minutes = (start_hour - current_hour) * 60 + (start_min - current_min)
                return max(0, minutes)
        
        if sorted_windows:
            first_window = sorted_windows[0]
            start_hour, start_min = map(int, first_window['start'].split(':'))
            current_hour = dt.hour
            current_min = dt.minute
            
            minutes = (start_hour - current_hour + 24) * 60 + (start_min - current_min)
            return max(0, minutes)
        
        return 0
    
    def get_current_session_name_for_channel(self, channel_id, dt=None):
        """Get current session name for channel"""
        if dt is None:
            dt = self.get_ist_now()
        
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        
        for window in windows:
            start = window['start']
            end = window['end']
            
            if start <= current_time < end:
                return window.get('name', f"{start}-{end}")
        
        return "Break"
    
    def get_next_session_time_for_channel(self, channel_id, dt=None):
        """Get next session start time for channel"""
        if dt is None:
            dt = self.get_ist_now()
        
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        
        sorted_windows = sorted(windows, key=lambda w: w['start'])
        
        for window in sorted_windows:
            if window['start'] > current_time:
                return window['start']
        
        if sorted_windows:
            return sorted_windows[0]['start']
        
        return "10:00"
    

    def is_after_last_session_for_channel(self, channel_id, dt=None):
        """Check if current time is after the last configured session for this channel"""
        if dt is None:
            dt = self.get_ist_now()
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        if not windows:
            return False
        last_window = sorted(windows, key=lambda w: w['end'])[-1]
        return current_time >= last_window['end']

    def format_session_time_range(self, start, end):
        """Format time range for display"""
        def format_12h(time_str):
            hour, minute = map(int, time_str.split(':'))
            period = "AM" if hour < 12 else "PM"
            hour12 = hour % 12
            if hour12 == 0:
                hour12 = 12
            return f"{hour12:02d}:{minute:02d} {period}"
        
        return f"{format_12h(start)}-{format_12h(end)}"
    
    def get_session_schedule_text(self, channel_id):
        """Get formatted schedule text for a channel"""
        windows = self.get_channel_time_windows(channel_id)
        
        if not windows:
            return "❌ No time windows configured"
        
        text = "🔖 PREDICTION TIME\n"
        for i, window in enumerate(windows, 1):
            start = window['start']
            end = window['end']
            time_range = self.format_session_time_range(start, end)
            text += f"🔔 {time_range}\n"
        
        return text

    async def send_via_user_account(self, chat_id, text=None, media_type=None, media_file=None, caption=None, media_group=None, context=None, filename_hint=None):
        """Send message using Pyrogram"""
        
        if not self.user_client_connected:
            logging.error("❌ User client not connected")
            return False

        chat_id_str = str(chat_id).strip()
        target_id = await self.get_chat_id(chat_id_str)
        
        if not target_id:
            logging.error(f"❌ Could not resolve chat ID for {chat_id}")
            return False
        
        try:
            if media_group and len(media_group) > 1:
                logging.info(f"📸 Sending media group with {len(media_group)} items to {chat_id}")
                
                pyrogram_media = []
                for i, media_item in enumerate(media_group):
                    file_id = media_item.get('media')
                    item_type = media_item.get('type', 'photo')
                    item_caption = media_item.get('caption', '') if i == 0 else None
                    
                    file_name = media_item.get('file_name', '')
                    detected_type, actual_type = self.detect_media_type_from_file(file_name)
                    
                    if detected_type == 'sticker':
                        await self.user_app.send_sticker(
                            chat_id=target_id,
                            sticker=file_id
                        )
                        continue
                    
                    if actual_type == 'photo' or detected_type == 'photo':
                        media = PyrogramInputMediaPhoto(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    elif actual_type == 'video' or detected_type == 'video':
                        media = PyrogramInputMediaVideo(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    elif actual_type == 'animation' or detected_type == 'animation':
                        media = PyrogramInputMediaAnimation(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    else:
                        media = PyrogramInputMediaDocument(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    
                    pyrogram_media.append(media)
                
                if pyrogram_media:
                    msgs = await self.user_app.send_media_group(
                        chat_id=target_id,
                        media=pyrogram_media
                    )
                    logging.info(f"✅ Media group sent via user account to {chat_id}")
                    return msgs
            
            elif media_type and media_file:
                detected_type, actual_type = self.detect_media_type_from_file(filename_hint)

                temp_path = None
                upload_media = media_file
                try:
                    if context is not None and isinstance(media_file, str):
                        file_obj = await context.bot.get_file(media_file)
                        suffix = ''
                        if filename_hint:
                            suffix = os.path.splitext(str(filename_hint))[-1]
                        elif getattr(file_obj, 'file_path', None):
                            suffix = os.path.splitext(str(file_obj.file_path))[-1]
                        with tempfile.NamedTemporaryFile(delete=False, suffix=suffix) as tmp:
                            temp_path = tmp.name
                        await file_obj.download_to_drive(custom_path=temp_path)
                        upload_media = temp_path
                except Exception as e:
                    logging.warning(f"⚠️ User account media download failed, trying direct file_id: {e}")
                    upload_media = media_file

                if media_type == 'sticker' or detected_type == 'sticker' or actual_type == 'sticker':
                    msg = await self.user_app.send_sticker(
                        chat_id=target_id,
                        sticker=upload_media
                    )
                elif media_type == 'photo' or detected_type == 'photo' or actual_type == 'photo':
                    msg = await self.user_app.send_photo(
                        chat_id=target_id,
                        photo=upload_media,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'video' or detected_type == 'video' or actual_type == 'video':
                    msg = await self.user_app.send_video(
                        chat_id=target_id,
                        video=upload_media,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'animation' or detected_type == 'animation' or actual_type == 'animation':
                    msg = await self.user_app.send_animation(
                        chat_id=target_id,
                        animation=upload_media,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'voice' or detected_type == 'voice':
                    msg = await self.user_app.send_voice(
                        chat_id=target_id,
                        voice=upload_media,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                else:
                    msg = await self.user_app.send_document(
                        chat_id=target_id,
                        document=upload_media,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )

                if temp_path:
                    try:
                        os.unlink(temp_path)
                    except Exception:
                        pass

                logging.info(f"✅ Media sent via user account to {chat_id}")
                return msg
            
            else:
                if not text or not text.strip():
                    logging.error(f"❌ Text is empty for {chat_id}!")
                    return False
                
                msg = await self.user_app.send_message(
                    chat_id=target_id,
                    text=text,
                    parse_mode=PyrogramParseMode.HTML
                )
                logging.info(f"✅ Text sent via user account to {chat_id}")
                return msg
            
        except FloodWait as e:
            logging.warning(f"⚠️ FloodWait: Waiting {e.value}s")
            await asyncio.sleep(e.value)
            return False
            
        except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
            logging.error(f"❌ Cannot access channel {chat_id}: {e}")
            self.failed_channels.add(chat_id_str)
            return False
            
        except Exception as e:
            logging.error(f"❌ User account send failed for {chat_id}: {e}")
            return False

    def _extract_message_id(self, result):
        if not result:
            return None
        try:
            if isinstance(result, list) and result:
                msg = result[0]
                return getattr(msg, 'id', None) or getattr(msg, 'message_id', None)
            return getattr(result, 'id', None) or getattr(result, 'message_id', None)
        except Exception:
            return None

    def strip_premium_emoji_tags(self, text: str):
        if not text:
            return text
        return re.sub(r'<emoji[^>]*>([^<]*)</emoji>', r'\1', text)

    def normalize_premium_emoji_tags(self, text: str):
        if not text:
            return text
        text = re.sub(r'<emoji[^>]*>([^<]*)</emoji>', r'\1', text)
        text = re.sub(r'<tg-emoji[^>]*>([^<]*)</tg-emoji>', r'\1', text)
        return text

    async def delete_channel_message(self, context: ContextTypes.DEFAULT_TYPE, chat_id, message_id):
        try:
            if self.use_user_account and self.user_app and self.user_client_connected:
                target_id = await self.get_chat_id(chat_id)
                if target_id:
                    await self.user_app.delete_messages(target_id, message_id)
            else:
                await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
            return True
        except Exception as e:
            logging.error(f"❌ Failed to delete message {message_id} in {chat_id}: {e}")
            return False

    async def send_message_with_retry(self, context: ContextTypes.DEFAULT_TYPE, chat_id, text=None, max_retries=3, for_channel=False, media_type=None, media_file=None, caption=None, media_group=None, parse_mode=None, filename_hint=None):
        """Send message with retry logic"""
        
        for attempt in range(max_retries):
            try:
                if media_group and len(media_group) == 1:
                    single = media_group[0]
                    media_type = single.get('type')
                    media_file = single.get('media')
                    caption = single.get('caption')
                    filename_hint = single.get('file_name')
                    media_group = None

                has_media = bool(media_group or (media_type and media_file))
                has_caption = False
                if media_group and len(media_group) > 1:
                    has_caption = any(m.get('caption') for m in media_group)
                elif media_type and media_file:
                    has_caption = bool(caption)
                if has_media and not has_caption:
                    for_channel = False

                if for_channel and self.use_user_account and self.user_client_connected:
                    success = await self.send_via_user_account(
                        chat_id, text, media_type, media_file, caption, media_group, context, filename_hint
                    )
                    if success:
                        return success
                    else:
                        logging.warning("⚠️ User account failed, falling back to bot")
                
                if media_group and len(media_group) > 1:
                    logging.info(f"📸 Sending media group via bot to {chat_id}")
                    
                    telegram_media = []
                    for i, media_item in enumerate(media_group):
                        caption_text = media_item.get('caption', '')
                        mtype = media_item.get('type', 'photo')
                        file_name = str(media_item.get('file_name', '')).lower()
                        
                        if not file_name:
                            actual_type = mtype
                        else:
                            _, actual_type = self.detect_media_type_from_file(file_name)
                        
                        if actual_type == 'sticker':
                            logging.warning(f"⚠️ Sticker can't be in media group, skipping")
                            continue
                        
                        if actual_type == 'photo':
                            media = InputMediaPhoto(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif actual_type == 'video':
                            media = InputMediaVideo(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif actual_type == 'animation':
                            media = InputMediaAnimation(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        else:
                            media = InputMediaDocument(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        
                        telegram_media.append(media)
                    
                    if telegram_media:
                        result = await context.bot.send_media_group(
                            chat_id=chat_id,
                            media=telegram_media
                        )
                        logging.info(f"✅ Media group sent to {chat_id}")
                        return result
                
                elif media_type and media_file:
                    detected_type, actual_type = self.detect_media_type_from_file(filename_hint)
                    
                    if actual_type == 'sticker':
                        result = await context.bot.send_sticker(
                            chat_id=chat_id,
                            sticker=media_file
                        )
                    elif actual_type == 'photo':
                        result = await context.bot.send_photo(
                            chat_id=chat_id,
                            photo=media_file,
                            caption=caption,
                            parse_mode=None
                        )
                    elif actual_type == 'video':
                        result = await context.bot.send_video(
                            chat_id=chat_id,
                            video=media_file,
                            caption=caption,
                            parse_mode=None
                        )
                    elif actual_type == 'animation':
                        result = await context.bot.send_animation(
                            chat_id=chat_id,
                            animation=media_file,
                            caption=caption,
                            parse_mode=None
                        )
                    elif actual_type == 'voice':
                        result = await context.bot.send_voice(
                            chat_id=chat_id,
                            voice=media_file,
                            caption=caption,
                            parse_mode=None
                        )
                    else:
                        result = await context.bot.send_document(
                            chat_id=chat_id,
                            document=media_file,
                            caption=caption,
                            parse_mode=None
                        )
                    
                    logging.info(f"✅ Media sent to {chat_id}")
                    return result
                
                else:
                    if not text or not text.strip():
                        logging.error(f"❌ Text is empty for {chat_id}!")
                        return False
                    
                    clean_text = self.strip_premium_emoji_tags(text)
                    
                    if not clean_text or not clean_text.strip():
                        logging.error("❌ Clean text is empty!")
                        return False
                    
                    result = await context.bot.send_message(
                        chat_id=chat_id,
                        text=clean_text,
                        parse_mode=None
                    )
                    logging.info(f"✅ Text message sent to {chat_id}")
                    return result
                
            except NetworkError as e:
                logging.warning(f"⚠️ Network error on attempt {attempt + 1}/{max_retries}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                    
            except TimedOut as e:
                logging.warning(f"⚠️ Timeout on attempt {attempt + 1}/{max_retries}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                    
            except RetryAfter as e:
                logging.warning(f"⚠️ Rate limited, waiting {e.retry_after}s")
                await asyncio.sleep(e.retry_after)
                
            except Exception as e:
                logging.error(f"❌ Error sending message to {chat_id}: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
        
        return False

    def load_config(self):
        """Load configuration with channel-specific settings"""
        default_config = {
            "admin_ids": [6484788124],
            "channels": [],
            "channel_configs": {},
            "channel_prediction_status": {},
            "channel_subscriptions": {},
            "channel_time_windows": {},
            "custom_break_messages": {},
            "custom_break_schedules": {},
            "custom_break_duration": 60,
            "event_media": {},
            "api_url": "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json"
        }

        try:
            mongo_doc = self._mongo_get_doc('config')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                loaded_config = mongo_doc['data']
                self.config = {**default_config, **loaded_config}
            elif os.path.exists(self.config_file):
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    loaded_config = json.load(f)
                self.config = {**default_config, **loaded_config}
                self._mongo_upsert_doc('config', loaded_config)
                logging.info("✅ Config migrated from JSON to MongoDB")
            else:
                self.config = default_config.copy()
                self.active_channels = []
                self.channel_configs = {}
                self.channel_prediction_status = {}
                self.channel_subscriptions = {}
                self.channel_time_windows = {}
                self.custom_break_messages = {}
                self.custom_break_schedules = {}
                self.event_media = {}
                self.save_config()
                logging.info("✅ Created new config in MongoDB")
                return

            self.active_channels = self.config.get('channels', [])
            self.channel_configs = self.config.get('channel_configs', {})
            self.channel_prediction_status = self.config.get('channel_prediction_status', {})
            self.channel_subscriptions = self.config.get('channel_subscriptions', {})
            self.channel_time_windows = self.config.get('channel_time_windows', {})
            self.custom_break_messages = self.config.get('custom_break_messages', {})
            self.custom_break_schedules = self.config.get('custom_break_schedules', {})
            self.custom_break_duration = self.config.get('custom_break_duration', 60)
            self.event_media = self.config.get('event_media', {})

            for channel_id, config in self.channel_configs.items():
                if 'templates' not in config or not isinstance(config.get('templates'), dict):
                    config['templates'] = {}
                for t_key, t_val in self.default_templates.items():
                    config['templates'].setdefault(t_key, t_val)

                if 'show_links' not in config:
                    config['show_links'] = True
                if 'show_promo' not in config:
                    config['show_promo'] = True
                if channel_id not in self.channel_prediction_status:
                    self.channel_prediction_status[channel_id] = True
            
            for i, channel in enumerate(self.active_channels):
                if channel not in self.channel_time_windows:
                    self.channel_time_windows[channel] = self._get_default_windows_for_channel(i)

            logging.info(f"✅ Configuration loaded. Active channels: {len(self.active_channels)}")
            logging.info(f"✅ Time windows loaded for {len(self.channel_time_windows)} channels")

            for channel_id, messages in self.custom_break_messages.items():
                if isinstance(messages, dict):
                    self.custom_break_messages[channel_id] = [messages]
                elif not isinstance(messages, list):
                    self.custom_break_messages[channel_id] = []

            for channel_id, media_dict in self.event_media.items():
                for event_type in self.message_types.keys():
                    if event_type not in media_dict:
                        media_dict[event_type] = []

        except Exception as e:
            logging.error(f"❌ Error loading config: {e}")
            self.config = default_config.copy()
            self.active_channels = []
            self.channel_configs = {}
            self.channel_prediction_status = {}
            self.channel_subscriptions = {}
            self.channel_time_windows = {}
            self.custom_break_messages = {}
            self.custom_break_schedules = {}
            self.event_media = {}
            self.save_config()

    def save_config(self):
        """Save configuration"""
        try:
            self.config['channels'] = self.active_channels
            self.config['channel_configs'] = self.channel_configs
            self.config['channel_prediction_status'] = self.channel_prediction_status
            self.config['channel_subscriptions'] = self.channel_subscriptions
            self.config['channel_time_windows'] = self.channel_time_windows
            self.config['custom_break_messages'] = self.custom_break_messages
            self.config['custom_break_schedules'] = self.custom_break_schedules
            self.config['custom_break_duration'] = self.custom_break_duration
            self.config['event_media'] = self.event_media

            if self._mongo_upsert_doc('config', self.config):
                logging.info(f"✅ Configuration saved to MongoDB")
            else:
                logging.error("❌ Configuration save skipped")
        except Exception as e:
            logging.error(f"❌ Error saving config: {e}")

    def get_channel_config(self, channel_id):
        """Get channel-specific config or create default"""
        if channel_id not in self.channel_configs:
            self.channel_configs[channel_id] = {
                'register_link': "https://bdgsg.com//#/register?invitationCode=5151329947",
                'promotional_text': "{gift} Register now and get DAILY FREE GIFT CODE! {gift}",
                'show_links': True,
                'show_promo': True,
                'templates': self.default_templates.copy(),
                'custom_break_enabled': False,
                'custom_break_delay': 5,
                'custom_break_mode': 'sequential',
                'prediction_start_hour': 7,
                'prediction_end_hour': 24
            }
            self.save_config()
        
        config = self.channel_configs[channel_id]
        if 'show_links' not in config:
            config['show_links'] = True
        if 'show_promo' not in config:
            config['show_promo'] = True
        if 'templates' not in config:
            config['templates'] = self.default_templates.copy()
            self.save_config()
        if 'custom_break_mode' not in config:
            config['custom_break_mode'] = 'sequential'
            self.save_config()
        if 'prediction_start_hour' not in config:
            config['prediction_start_hour'] = 7
            self.save_config()
        if 'prediction_end_hour' not in config:
            config['prediction_end_hour'] = 24
            self.save_config()

        return config

    def update_channel_config(self, channel_id, updates):
        """Update channel-specific config"""
        config = self.get_channel_config(channel_id)
        
        if 'templates' in updates:
            config['templates'].update(updates['templates'])
            del updates['templates']
        
        config.update(updates)
        self.channel_configs[channel_id] = config
        self.save_config()
        return config

    def parse_time_12h(self, time_str: str):
        try:
            s = time_str.strip().upper()
            if re.match(r"^\d{1,2}\s*(AM|PM)$", s):
                s = s.replace(" ", "")
                hour = int(s[:-2])
                minute = 0
                mer = s[-2:]
            else:
                m = re.match(r"^(\d{1,2}):(\d{2})\s*(AM|PM)$", s)
                if not m:
                    return None
                hour = int(m.group(1))
                minute = int(m.group(2))
                mer = m.group(3)
            if hour < 1 or hour > 12 or minute < 0 or minute > 59:
                return None
            if mer == "AM":
                hour = 0 if hour == 12 else hour
            else:
                hour = 12 if hour == 12 else hour + 12
            return hour, minute
        except Exception:
            return None

    def format_time_12h(self, hour: int, minute: int):
        mer = "AM" if hour < 12 else "PM"
        h = hour % 12
        if h == 0:
            h = 12
        return f"{h:02d}:{minute:02d} {mer}"

    def get_ist_now(self):
        utc_now = datetime.utcnow()
        return utc_now + timedelta(hours=5, minutes=30)

    def set_channel_subscription_days(self, channel_id, days: int):
        now = self.get_ist_now()
        expires = now + timedelta(days=max(1, int(days)))
        self.channel_subscriptions[channel_id] = {
            'days': int(days),
            'expires_at': expires.isoformat(),
            'alert_1d_sent': False,
            'expired_sent': False,
        }
        self.save_config()
        return self.channel_subscriptions[channel_id]

    def is_channel_subscription_active(self, channel_id):
        sub = self.channel_subscriptions.get(channel_id)
        if not sub:
            return True
        try:
            exp = datetime.fromisoformat(sub.get('expires_at'))
            return self.get_ist_now() < exp
        except Exception:
            return True

    async def process_subscription_status(self, context: ContextTypes.DEFAULT_TYPE):
        if not self.channel_subscriptions:
            return
        now = self.get_ist_now()
        admin_id = 6484788124
        for ch, sub in list(self.channel_subscriptions.items()):
            try:
                exp = datetime.fromisoformat(sub.get('expires_at'))
            except Exception:
                continue
            remaining = exp - now
            if timedelta(0) < remaining <= timedelta(days=1) and not sub.get('alert_1d_sent'):
                sub['alert_1d_sent'] = True
                if admin_id:
                    try:
                        await context.bot.send_message(admin_id, f"⚠️ Subscription Expiry Alert\nChannel: {ch}\nExpiry: {sub.get('expires_at')}\nAction: Renew to avoid auto-pause.")
                    except Exception:
                        pass
            if remaining <= timedelta(0):
                if self.channel_prediction_status.get(ch, True):
                    self.channel_prediction_status[ch] = False
                if not sub.get('expired_sent') and admin_id:
                    sub['expired_sent'] = True
                    try:
                        await context.bot.send_message(admin_id, f"⛔ Subscription Expired\nChannel: {ch}\nStatus: Predictions auto-paused.\nAction: Renew subscription to resume.")
                    except Exception:
                        pass
        self.save_config()

    def get_channel_template(self, channel_id, template_key):
        config = self.get_channel_config(channel_id)
        return config['templates'].get(template_key, self.default_templates.get(template_key, ''))

    def is_channel_enabled(self, channel_id):
        return self.channel_prediction_status.get(channel_id, True) and self.is_channel_subscription_active(channel_id)

    def _is_channel_in_time_window_raw(self, channel_id, dt):
        current_time = dt.strftime("%H:%M")
        windows = self.get_channel_time_windows(channel_id)
        
        for window in windows:
            start = window['start']
            end = window['end']
            
            if start <= current_time < end:
                return True
        
        return False
    
    def is_channel_in_time_window(self, channel_id, hour=None):
        if hour is None:
            dt = self.get_ist_now()
        elif isinstance(hour, int):
            dt = self.get_ist_now().replace(hour=hour)
        else:
            dt = hour
        
        return self._is_channel_in_time_window_raw(channel_id, dt)

    def is_channel_break_slot(self, channel_id, hour=None):
        if hour is None:
            dt = self.get_ist_now()
        else:
            dt = self.get_ist_now().replace(hour=hour)
        return not self.is_channel_in_time_window(channel_id, dt)

    def get_next_session_label_for_channel(self, channel_id, hour=None):
        if hour is None:
            dt = self.get_ist_now()
        else:
            dt = self.get_ist_now().replace(hour=hour)
        return self.get_next_session_time_for_channel(channel_id, dt)

    def is_channel_prediction_active(self, channel_id):
        return self.is_channel_enabled(channel_id)

    def toggle_channel_prediction(self, channel_id):
        current_status = self.channel_prediction_status.get(channel_id, True)
        self.channel_prediction_status[channel_id] = not current_status
        self.save_config()
        return self.channel_prediction_status[channel_id]

    def set_channel_prediction_status(self, channel_id, status):
        self.channel_prediction_status[channel_id] = status
        self.save_config()
        return status

    def get_custom_break_messages(self, channel_id):
        messages = self.custom_break_messages.get(channel_id, [])
        if isinstance(messages, dict):
            messages = [messages]
        elif not isinstance(messages, list):
            messages = []
        return messages

    def get_custom_break_message_by_index(self, channel_id, index):
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            return messages[index]
        return None

    def add_custom_break_message(self, channel_id, message_data):
        if channel_id not in self.custom_break_messages:
            self.custom_break_messages[channel_id] = []
        
        if not isinstance(self.custom_break_messages[channel_id], list):
            self.custom_break_messages[channel_id] = []
        
        self.custom_break_messages[channel_id].append(message_data)
        self.save_config()
        return len(self.custom_break_messages[channel_id]) - 1

    def update_custom_break_message(self, channel_id, index, message_data):
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            self.custom_break_messages[channel_id][index] = message_data
            self.save_config()
            return True
        return False

    def delete_custom_break_message(self, channel_id, index=None):
        if channel_id in self.custom_break_messages:
            if index is None:
                del self.custom_break_messages[channel_id]
                self.save_config()
                return True
            elif isinstance(self.custom_break_messages[channel_id], list) and 0 <= index < len(self.custom_break_messages[channel_id]):
                self.custom_break_messages[channel_id].pop(index)
                if not self.custom_break_messages[channel_id]:
                    del self.custom_break_messages[channel_id]
                self.save_config()
                return True
        return False

    def get_next_custom_break_index(self, channel_id):
        channel_config = self.get_channel_config(channel_id)
        
        if channel_id not in self.custom_break_schedules:
            self.custom_break_schedules[channel_id] = 0
            self.save_config()
        
        messages = self.get_custom_break_messages(channel_id)
        if not messages:
            return None
        
        mode = channel_config.get('custom_break_mode', 'sequential')
        
        if mode == 'sequential':
            current_idx = self.custom_break_schedules[channel_id]
            self.custom_break_schedules[channel_id] = (current_idx + 1) % len(messages)
            self.save_config()
            return current_idx
        else:
            return random.randint(0, len(messages) - 1)

    def format_custom_message_with_premium_emojis(self, text, channel_id):
        if not text:
            return text
        
        try:
            text = self.auto_detect_and_convert_message(text)
            return self.convert_placeholder_to_premium_emoji(text, for_channel=True)
        except Exception as e:
            logging.error(f"❌ Error formatting custom message: {e}")
            return text

    def format_placeholders(self, text, channel_id, **kwargs):
        if not text:
            return text

        channel_config = self.get_channel_config(channel_id)
        format_dict = {
            'register_link': channel_config.get('register_link', ''),
            'promo_text': channel_config.get('promotional_text', ''),
            'session': kwargs.get('session', ''),
            'next_session': kwargs.get('next_session', ''),
            'wins': kwargs.get('wins', 0),
            'losses': kwargs.get('losses', 0),
            'win_rate': kwargs.get('win_rate', 0),
            'break_duration': kwargs.get('break_duration', self.custom_break_duration),
            'period': kwargs.get('period', ''),
            'prediction': kwargs.get('prediction', ''),
        }

        for k, v in kwargs.items():
            if k not in format_dict:
                format_dict[k] = v

        for key, val in format_dict.items():
            text = text.replace(f"{{{key}}}", str(val))
        return text

    def normalize_event_type(self, event_type):
        if event_type == 'session_end':
            return 'break'
        return event_type

    def get_event_media(self, channel_id, event_type):
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media:
            return []
        return self.event_media[channel_id].get(event_type, [])

    def add_event_media(self, channel_id, event_type, media_item):
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media:
            self.event_media[channel_id] = {event_type: []}
        
        if event_type not in self.event_media[channel_id]:
            self.event_media[channel_id][event_type] = []
        
        self.event_media[channel_id][event_type].append(media_item)
        self.save_config()
        return len(self.event_media[channel_id][event_type]) - 1

    def update_event_media(self, channel_id, event_type, index, media_item):
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media or event_type not in self.event_media[channel_id]:
            return False
        
        if 0 <= index < len(self.event_media[channel_id][event_type]):
            self.event_media[channel_id][event_type][index] = media_item
            self.save_config()
            return True
        return False

    def delete_event_media(self, channel_id, event_type, index=None):
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media or event_type not in self.event_media[channel_id]:
            return False
        
        if index is None:
            self.event_media[channel_id][event_type] = []
            self.save_config()
            return True
        elif 0 <= index < len(self.event_media[channel_id][event_type]):
            self.event_media[channel_id][event_type].pop(index)
            self.save_config()
            return True
        return False

    def get_custom_messages(self, channel_id, message_type):
        if channel_id not in self.custom_messages:
            return []
        return self.custom_messages[channel_id].get(message_type, [])

    def add_custom_message_simple(self, channel_id, message_type, message_data):
        if channel_id not in self.custom_messages:
            self.custom_messages[channel_id] = {}
        
        if message_type not in self.custom_messages[channel_id]:
            self.custom_messages[channel_id][message_type] = []
        
        self.custom_messages[channel_id][message_type].append(message_data)
        self.save_custom_messages()
        return len(self.custom_messages[channel_id][message_type]) - 1

    def delete_custom_message(self, channel_id, message_type, index=None):
        if channel_id not in self.custom_messages or message_type not in self.custom_messages[channel_id]:
            return False
        
        if index is None:
            del self.custom_messages[channel_id][message_type]
            self.save_custom_messages()
            return True
        elif 0 <= index < len(self.custom_messages[channel_id][message_type]):
            self.custom_messages[channel_id][message_type].pop(index)
            if not self.custom_messages[channel_id][message_type]:
                del self.custom_messages[channel_id][message_type]
            self.save_custom_messages()
            return True
        return False

    def save_custom_messages(self):
        try:
            if self._mongo_upsert_doc('custom_messages', self.custom_messages):
                logging.info("✅ Custom messages saved to MongoDB")
        except Exception as e:
            logging.error(f"❌ Error saving custom messages: {e}")

    def format_promo_text_with_emojis(self, text, for_channel=False):
        if not text:
            return ""
        
        try:
            text = self.auto_detect_and_convert_message(text)
            return self.convert_placeholder_to_premium_emoji(text, for_channel)
        except Exception as e:
            logging.error(f"❌ Error formatting promo text: {e}")
            return text

    def load_emoji_config(self):
        default_emoji_config = {
            "premium_emojis": {
                "fire": "<emoji id=5420315771991497307>🔥</emoji>",
                "crown": "<emoji id=6266995104687330978>👑</emoji>",
                "sparkles": "<emoji id=6285088169817805553>✨</emoji>",
                "rocket": "<emoji id=5188481279963715781>🚀</emoji>",
                "money": "<emoji id=6267068789146260253>💰</emoji>",
                "chart": "<emoji id=5431577498364158238>📊</emoji>",
                "target": "<emoji id=5310278924616356636>🎯</emoji>",
                "trophy": "<emoji id=5413566144986503832>🏆</emoji>",
                "gift": "<emoji id=5384578448633129482>🎁</emoji>",
                "lightning": "<emoji id=6267107057304868214>⚡</emoji>",
                "star": "<emoji id=5435957248314579621>⭐</emoji>",
                "warning": "<emoji id=6267039884016358504>⚠️</emoji>",
                "check": "<emoji id=6267008582294705964>✅</emoji>",
                "cross": "<emoji id=5343968063970632884>❌</emoji>",
                "clock": "<emoji id=5386415655253730366>⏰</emoji>",
                "link": "<emoji id=4958689671950369798>🔗</emoji>",
                "moon": "<emoji id=5208554136039073738>🌙</emoji>",
                "sun": "<emoji id=5413883478645169306>🌅</emoji>",
                "coffee": "<emoji id=5451959871257713464>☕</emoji>",
                "sleep": "<emoji id=5359543311897998264>💤</emoji>",
                "break_icon": "<emoji id=5359543311897998264>⏸️</emoji>",
                "reload": "<emoji id=5264727218734524899>🔄</emoji>",
                "party": "<emoji id=5436040291507247633>🎉</emoji>",
                "money_loss": "<emoji id=5472030678633684592>💸</emoji>",
                "star2": "<emoji id=5458799228719472718>🌟</emoji>",
            },
            "regular_emojis": {
                "fire": "🔥",
                "crown": "👑",
                "sparkles": "✨",
                "rocket": "🚀",
                "money": "💰",
                "chart": "📊",
                "target": "🎯",
                "trophy": "🏆",
                "gift": "🎁",
                "lightning": "⚡",
                "star": "⭐",
                "warning": "⚠️",
                "check": "✅",
                "cross": "❌",
                "clock": "⏰",
                "link": "🔗",
                "moon": "🌙",
                "sun": "🌅",
                "coffee": "☕",
                "sleep": "💤",
                "break_icon": "⏸️",
                "reload": "🔄",
                "party": "🎉",
                "money_loss": "💸",
                "star2": "🌟"
            },
            "emoji_to_placeholder": {
                "🔥": "{fire}",
                "👑": "{crown}",
                "✨": "{sparkles}",
                "🚀": "{rocket}",
                "💰": "{money}",
                "📊": "{chart}",
                "🎯": "{target}",
                "🏆": "{trophy}",
                "🎁": "{gift}",
                "⚡": "{lightning}",
                "⭐": "{star}",
                "⚠️": "{warning}",
                "✅": "{check}",
                "❌": "{cross}",
                "⏰": "{clock}",
                "🔗": "{link}",
                "🌙": "{moon}",
                "🌅": "{sun}",
                "☕": "{coffee}",
                "💤": "{sleep}",
                "⏸️": "{break_icon}",
                "🔄": "{reload}",
                "🎉": "{party}",
                "💸": "{money_loss}",
                "🌟": "{star2}"
            },
            "placeholder_to_emoji": {
                "{fire}": "🔥",
                "{crown}": "👑",
                "{sparkles}": "✨",
                "{rocket}": "🚀",
                "{money}": "💰",
                "{chart}": "📊",
                "{target}": "🎯",
                "{trophy}": "🏆",
                "{gift}": "🎁",
                "{lightning}": "⚡",
                "{star}": "⭐",
                "{warning}": "⚠️",
                "{check}": "✅",
                "{cross}": "❌",
                "{clock}": "⏰",
                "{link}": "🔗",
                "{moon}": "🌙",
                "{sun}": "🌅",
                "{coffee}": "☕",
                "{sleep}": "💤",
                "{break_icon}": "⏸️",
                "{reload}": "🔄",
                "{party}": "🎉",
                "{money_loss}": "💸",
                "{star2}": "🌟"
            }
        }
        
        try:
            mongo_doc = self._mongo_get_doc('emoji_config')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                self.emoji_config = mongo_doc['data']
                logging.info("✅ Emoji configuration loaded from MongoDB")
            elif os.path.exists(self.emoji_config_file):
                with open(self.emoji_config_file, 'r', encoding='utf-8') as f:
                    self.emoji_config = json.load(f)
                self._mongo_upsert_doc('emoji_config', self.emoji_config)
                logging.info("✅ Emoji configuration migrated from JSON")
            else:
                self.emoji_config = default_emoji_config
                self.save_emoji_config()
                logging.info("✅ Created default emoji configuration in MongoDB")
        except Exception as e:
            logging.error(f"❌ Error loading emoji config: {e}")
            self.emoji_config = default_emoji_config
            self.save_emoji_config()
        
        self.ensure_emoji_config_keys()

    def save_emoji_config(self):
        try:
            if self._mongo_upsert_doc('emoji_config', self.emoji_config):
                logging.info("✅ Emoji configuration saved to MongoDB")
        except Exception as e:
            logging.error(f"❌ Error saving emoji config: {e}")

    def get_emoji(self, emoji_key, for_channel=False):
        try:
            if for_channel and self.use_user_account:
                return self.emoji_config['premium_emojis'].get(emoji_key, self.emoji_config['regular_emojis'].get(emoji_key, ''))
            else:
                return self.emoji_config['regular_emojis'].get(emoji_key, '')
        except KeyError:
            regular_emojis = {
                "fire": "🔥", "crown": "👑", "sparkles": "✨", "rocket": "🚀",
                "money": "💰", "chart": "📊", "target": "🎯", "trophy": "🏆",
                "gift": "🎁", "lightning": "⚡", "star": "⭐", "warning": "⚠️",
                "check": "✅", "cross": "❌", "clock": "⏰", "link": "🔗",
                "moon": "🌙", "sun": "🌅", "coffee": "☕", "sleep": "💤",
                "break_icon": "⏸️", "reload": "🔄", "party": "🎉", "money_loss": "💸", "star2": "🌟"
            }
            return regular_emojis.get(emoji_key, '')

    def convert_regular_emoji_to_placeholder(self, text):
        if not text:
            return text
        
        try:
            if 'emoji_to_placeholder' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in text:
                    text = text.replace(emoji, placeholder)
        
        except Exception as e:
            logging.error(f"❌ Error converting emojis to placeholders: {e}")
            pass
        
        return text

    def convert_placeholder_to_premium_emoji(self, text, for_channel=False):
        if not text:
            return text
        
        try:
            if 'placeholder_to_emoji' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            if not for_channel or not self.use_user_account:
                for placeholder, emoji in self.emoji_config['placeholder_to_emoji'].items():
                    if placeholder in text:
                        text = text.replace(placeholder, emoji)
                return text
            
            if for_channel and self.use_user_account:
                for placeholder, premium_emoji in self.emoji_config['premium_emojis'].items():
                    placeholder_format = f"{{{placeholder}}}"
                    if placeholder_format in text:
                        text = text.replace(placeholder_format, premium_emoji)
            
            if 'placeholder_to_emoji' in self.emoji_config:
                for placeholder, emoji in self.emoji_config['placeholder_to_emoji'].items():
                    if placeholder in text:
                        text = text.replace(placeholder, emoji)
        
        except Exception as e:
            logging.error(f"❌ Error converting placeholders to emojis: {e}")
            basic_replacements = {
                "{fire}": "🔥", "{crown}": "👑", "{sparkles}": "✨", "{rocket}": "🚀",
                "{money}": "💰", "{chart}": "📊", "{target}": "🎯", "{trophy}": "🏆",
                "{gift}": "🎁", "{lightning}": "⚡", "{star}": "⭐", "{warning}": "⚠️",
                "{check}": "✅", "{cross}": "❌", "{clock}": "⏰", "{link}": "🔗",
                "{moon}": "🌙", "{sun}": "🌅", "{coffee}": "☕", "{sleep}": "💤",
                "{break_icon}": "⏸️", "{reload}": "🔄", "{party}": "🎉", "{money_loss}": "💸", "{star2}": "🌟"
            }
            for placeholder, emoji in basic_replacements.items():
                if placeholder in text:
                    text = text.replace(placeholder, emoji)
        
        return text

    def format_with_emojis(self, text, for_channel=False):
        return self.convert_placeholder_to_premium_emoji(text, for_channel)

    def extract_emojis_from_text(self, text):
        if not text:
            return text, []
        
        emojis_found = []
        placeholder_text = text
        
        try:
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in text:
                    emojis_found.append(emoji)
                    placeholder_text = placeholder_text.replace(emoji, placeholder)
        except Exception as e:
            logging.error(f"❌ Error extracting emojis: {e}")
        
        return placeholder_text, emojis_found

    def auto_detect_and_convert_message(self, message_text):
        if not message_text:
            return message_text
        
        try:
            if 'emoji_to_placeholder' not in self.emoji_config:
                self.ensure_emoji_config_keys()
            
            converted_text = message_text
            
            emojis_found = []
            for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                if emoji in converted_text:
                    emojis_found.append(f"{emoji}->{placeholder}")
                    converted_text = converted_text.replace(emoji, placeholder)
            
            try:
                import emoji as _emoji_mod
                _emoji_available = True
            except ImportError:
                _emoji_mod = None
                _emoji_available = False

            emoji_list = _emoji_mod.emoji_list(message_text) if _emoji_available else []
            for emoji_data in emoji_list:
                emoji_char = emoji_data['emoji']
                if emoji_char not in self.emoji_config['emoji_to_placeholder']:
                    emoji_name = _emoji_mod.demojize(emoji_char).replace(':', '').replace('_', '')
                    placeholder = f"{{{emoji_name}}}"
                    
                    self.emoji_config['emoji_to_placeholder'][emoji_char] = placeholder
                    self.emoji_config['placeholder_to_emoji'][placeholder] = emoji_char
                    self.emoji_config['regular_emojis'][emoji_name] = emoji_char
                    
                    premium_emojis = {
                        "🔥": "<emoji id=5420315771991497307>🔥</emoji>",
                        "👑": "<emoji id=6266995104687330978>👑</emoji>",
                        "✨": "<emoji id=6285088169817805553>✨</emoji>",
                        "🚀": "<emoji id=5188481279963715781>🚀</emoji>",
                        "💰": "<emoji id=6267068789146260253>💰</emoji>",
                        "📊": "<emoji id=5431577498364158238>📊</emoji>",
                        "🎯": "<emoji id=5310278924616356636>🎯</emoji>",
                        "🏆": "<emoji id=5413566144986503832>🏆</emoji>",
                        "🎁": "<emoji id=5384578448633129482>🎁</emoji>",
                        "⚡": "<emoji id=6267107057304868214>⚡</emoji>",
                        "⭐": "<emoji id=5435957248314579621>⭐</emoji>",
                        "⚠️": "<emoji id=6267039884016358504>⚠️</emoji>",
                        "✅": "<emoji id=6267008582294705964>✅</emoji>",
                        "❌": "<emoji id=5343968063970632884>❌</emoji>",
                        "⏰": "<emoji id=5386415655253730366>⏰</emoji>",
                        "🔗": "<emoji id=4958689671950369798>🔗</emoji>",
                        "🌙": "<emoji id=5208554136039073738>🌙</emoji>",
                        "🌅": "<emoji id=5413883478645169306>🌅</emoji>",
                        "☕": "<emoji id=5451959871257713464>☕</emoji>",
                        "💤": "<emoji id=5359543311897998264>💤</emoji>",
                        "⏸️": "<emoji id=5359543311897998264>⏸️</emoji>",
                        "🔄": "<emoji id=5264727218734524899>🔄</emoji>",
                        "🎉": "<emoji id=5436040291507247633>🎉</emoji>",
                        "💸": "<emoji id=5472030678633684592>💸</emoji>",
                        "🌟": "<emoji id=5458799228719472718>🌟</emoji>",
                    }
                    if emoji_char in premium_emojis:
                        self.emoji_config['premium_emojis'][emoji_name] = premium_emojis[emoji_char]
                    
                    converted_text = converted_text.replace(emoji_char, placeholder)
            
            self.save_emoji_config()
            return converted_text
            
        except Exception as e:
            logging.error(f"❌ Error in auto-detect and convert: {e}")
            return message_text

    def ensure_emoji_config_keys(self):
        if not hasattr(self, 'emoji_config'):
            self.load_emoji_config()
        
        required_keys = ['premium_emojis', 'regular_emojis', 'emoji_to_placeholder', 'placeholder_to_emoji']
        
        for key in required_keys:
            if key not in self.emoji_config:
                if key == 'emoji_to_placeholder':
                    self.emoji_config[key] = {
                        "🔥": "{fire}",
                        "👑": "{crown}",
                        "✨": "{sparkles}",
                        "🚀": "{rocket}",
                        "💰": "{money}",
                        "📊": "{chart}",
                        "🎯": "{target}",
                        "🏆": "{trophy}",
                        "🎁": "{gift}",
                        "⚡": "{lightning}",
                        "⭐": "{star}",
                        "⚠️": "{warning}",
                        "✅": "{check}",
                        "❌": "{cross}",
                        "⏰": "{clock}",
                        "🔗": "{link}",
                        "🌙": "{moon}",
                        "🌅": "{sun}",
                        "☕": "{coffee}",
                        "💤": "{sleep}",
                        "⏸️": "{break_icon}",
                        "🔄": "{reload}",
                        "🎉": "{party}",
                        "💸": "{money_loss}",
                        "🌟": "{star2}"
                    }
                elif key == 'placeholder_to_emoji':
                    self.emoji_config[key] = {
                        "{fire}": "🔥",
                        "{crown}": "👑",
                        "{sparkles}": "✨",
                        "{rocket}": "🚀",
                        "{money}": "💰",
                        "{chart}": "📊",
                        "{target}": "🎯",
                        "{trophy}": "🏆",
                        "{gift}": "🎁",
                        "{lightning}": "⚡",
                        "{star}": "⭐",
                        "{warning}": "⚠️",
                        "{check}": "✅",
                        "{cross}": "❌",
                        "{clock}": "⏰",
                        "{link}": "🔗",
                        "{moon}": "🌙",
                        "{sun}": "🌅",
                        "{coffee}": "☕",
                        "{sleep}": "💤",
                        "{break_icon}": "⏸️",
                        "{reload}": "🔄",
                        "{party}": "🎉",
                        "{money_loss}": "💸",
                        "{star2}": "🌟"
                    }
                elif key not in self.emoji_config:
                    self.emoji_config[key] = {}
        
        self.emoji_config.setdefault('premium_emojis', {}).setdefault('airplane', '<emoji id=6165465711352223465>✈️</emoji>')
        self.emoji_config.setdefault('premium_emojis', {}).setdefault('dollarbanknote', '<emoji id=5409048419211682843>💵</emoji>')
        self.emoji_config.setdefault('premium_emojis', {}).setdefault('redexclamationmark', '<emoji id=6082526190604652379>❗️</emoji>')
        self.emoji_config.setdefault('regular_emojis', {}).setdefault('airplane', '✈️')
        self.emoji_config.setdefault('regular_emojis', {}).setdefault('dollarbanknote', '💵')
        self.emoji_config.setdefault('regular_emojis', {}).setdefault('redexclamationmark', '❗️')
        self.emoji_config.setdefault('emoji_to_placeholder', {}).setdefault('✈️', '{airplane}')
        self.emoji_config.setdefault('emoji_to_placeholder', {}).setdefault('💵', '{dollarbanknote}')
        self.emoji_config.setdefault('emoji_to_placeholder', {}).setdefault('❗️', '{redexclamationmark}')
        self.emoji_config.setdefault('emoji_to_placeholder', {}).setdefault('❗', '{redexclamationmark}')
        self.emoji_config.setdefault('placeholder_to_emoji', {}).setdefault('{airplane}', '✈️')
        self.emoji_config.setdefault('placeholder_to_emoji', {}).setdefault('{dollarbanknote}', '💵')
        self.emoji_config.setdefault('placeholder_to_emoji', {}).setdefault('{redexclamationmark}', '❗️')

        self.save_emoji_config()

    def initialize_configs(self):
        self.load_emoji_config()
        self.load_config()
        self.load_custom_messages()
        self.ensure_emoji_config_keys()

    def load_custom_messages(self):
        try:
            mongo_doc = self._mongo_get_doc('custom_messages')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                self.custom_messages = mongo_doc['data']
                logging.info(f"✅ Custom messages loaded from MongoDB: {len(self.custom_messages)} channels")
                return

            if os.path.exists(self.custom_messages_file):
                with open(self.custom_messages_file, 'r', encoding='utf-8') as f:
                    self.custom_messages = json.load(f)
                self._mongo_upsert_doc('custom_messages', self.custom_messages)
                logging.info(f"✅ Custom messages migrated from JSON: {len(self.custom_messages)} channels")
            else:
                self.custom_messages = {}
                self.save_custom_messages()
        except Exception as e:
            logging.error(f"❌ Error loading custom messages: {e}")
            self.custom_messages = {}

    # ==================== AI Methods ====================
    def initialize_ai_model(self):
        try:
            if os.path.exists(self.ai_model_file):
                with open(self.ai_model_file, 'rb') as f:
                    saved_data = pickle.load(f)
                    self.ai_model = saved_data.get('model')
                    self.scaler = saved_data.get('scaler')
                    self.pattern_database = saved_data.get('pattern_database', {})
                    self.ai_accuracy = saved_data.get('ai_accuracy', 0.0)
                    self.ai_correct_predictions = saved_data.get('ai_correct_predictions', 0)
                    self.ai_total_predictions = saved_data.get('ai_total_predictions', 0)
                logging.info(f"✅ AI Model loaded: Accuracy = {self.ai_accuracy:.2%}")
            else:
                self.ai_model = RandomForestClassifier(
                    n_estimators=100,
                    max_depth=10,
                    random_state=42,
                    n_jobs=-1
                )
                self.scaler = StandardScaler()
                self.pattern_database = {}
                logging.info("✅ New AI Model created")
                
            mongo_doc = self._mongo_get_doc('pattern_history')
            if mongo_doc and isinstance(mongo_doc.get('data'), list):
                self.pattern_history = mongo_doc['data']
                logging.info(f"✅ Pattern history loaded from MongoDB: {len(self.pattern_history)} patterns")
            elif os.path.exists(self.pattern_history_file):
                with open(self.pattern_history_file, 'r', encoding='utf-8') as f:
                    self.pattern_history = json.load(f)
                self._mongo_upsert_doc('pattern_history', self.pattern_history)
                logging.info(f"✅ Pattern history migrated from JSON: {len(self.pattern_history)} patterns")
                
        except Exception as e:
            logging.error(f"❌ Error initializing AI model: {e}")
            self.ai_model = RandomForestClassifier(
                n_estimators=100,
                max_depth=10,
                random_state=42,
                n_jobs=-1
            )
            self.scaler = StandardScaler()
            self.pattern_database = {}

    def save_ai_model(self):
        try:
            saved_data = {
                'model': self.ai_model,
                'scaler': self.scaler,
                'pattern_database': self.pattern_database,
                'ai_accuracy': self.ai_accuracy,
                'ai_correct_predictions': self.ai_correct_predictions,
                'ai_total_predictions': self.ai_total_predictions
            }
            with open(self.ai_model_file, 'wb') as f:
                pickle.dump(saved_data, f)
            
            self._mongo_upsert_doc('pattern_history', self.pattern_history)
                
            logging.info(f"✅ AI Model saved: Accuracy = {self.ai_accuracy:.2%}")
        except Exception as e:
            logging.error(f"❌ Error saving AI model: {e}")

    def extract_features_for_ai(self, results, numbers):
        features = []
        
        if len(results) < self.pattern_window_size:
            return [0] * self.feature_count
        
        result_numeric = [1 if r == 'BIG' else 0 for r in results]
        recent_results = result_numeric[:self.pattern_window_size]
        recent_numbers = numbers[:self.pattern_window_size]
        
        current_streak = 1
        for i in range(1, len(recent_results)):
            if recent_results[i] == recent_results[i-1]:
                current_streak += 1
            else:
                break
        features.append(current_streak)
        
        features.append(np.mean(recent_results[:3]))
        features.append(np.mean(recent_results[:5]))
        features.append(np.mean(recent_results[:10]))
        
        big_count = sum(recent_results)
        small_count = len(recent_results) - big_count
        features.append(big_count)
        features.append(small_count)
        features.append(big_count - small_count)
        
        big_numbers = sum(1 for n in recent_numbers if n >= 5)
        small_numbers = len(recent_numbers) - big_numbers
        features.append(big_numbers)
        features.append(small_numbers)
        
        alternating_score = 0
        for i in range(1, len(recent_results)):
            if recent_results[i] != recent_results[i-1]:
                alternating_score += 1
        features.append(alternating_score / len(recent_results))
        
        last_big_gap = 0
        last_small_gap = 0
        for i, r in enumerate(recent_results):
            if r == 1:
                last_big_gap = i
                break
        for i, r in enumerate(recent_results):
            if r == 0:
                last_small_gap = i
                break
        features.append(last_big_gap)
        features.append(last_small_gap)
        
        number_counts = [recent_numbers.count(i) for i in range(10)]
        features.extend(number_counts[:3])
        
        pattern_hash = self.calculate_pattern_hash(recent_results)
        pattern_type = self.identify_pattern_type(recent_results)
        pattern_score = self.pattern_database.get(pattern_hash, {}).get('success_rate', 0.5)
        features.append(pattern_score)
        
        if len(recent_results) >= 5:
            trend = np.polyfit(range(5), recent_results[:5], 1)[0]
            features.append(trend)
        else:
            features.append(0)
        
        changes = sum(1 for i in range(1, len(recent_results)) 
                     if recent_results[i] != recent_results[i-1])
        features.append(changes / len(recent_results))
        
        if len(features) < self.feature_count:
            features.extend([0] * (self.feature_count - len(features)))
        elif len(features) > self.feature_count:
            features = features[:self.feature_count]
            
        return features

    def calculate_pattern_hash(self, pattern):
        pattern_str = ''.join(str(int(x)) for x in pattern)
        return hashlib.md5(pattern_str.encode()).hexdigest()[:10]

    def identify_pattern_type(self, pattern):
        pattern = list(pattern)
        
        alternating = True
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                alternating = False
                break
        
        if alternating:
            return 'alternating'
        
        streak_count = 1
        max_streak = 1
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                streak_count += 1
                max_streak = max(max_streak, streak_count)
            else:
                streak_count = 1
        
        if max_streak >= 3:
            return 'streak'
        
        changes = sum(1 for i in range(1, len(pattern)) if pattern[i] != pattern[i-1])
        if changes >= len(pattern) * 0.7:
            return 'zigzag'
        
        clusters = 0
        in_cluster = False
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1] and not in_cluster:
                clusters += 1
                in_cluster = True
            elif pattern[i] != pattern[i-1]:
                in_cluster = False
        
        if clusters >= 2:
            return 'cluster'
        
        return 'random'

    def learn_from_pattern(self, pattern_hash, prediction, was_correct):
        if pattern_hash not in self.pattern_database:
            self.pattern_database[pattern_hash] = {
                'pattern': pattern_hash,
                'total_occurrences': 0,
                'correct_predictions': 0,
                'last_seen': datetime.now().isoformat(),
                'prediction_history': []
            }
        
        pattern_data = self.pattern_database[pattern_hash]
        pattern_data['total_occurrences'] += 1
        
        if was_correct:
            pattern_data['correct_predictions'] += 1
        
        pattern_data['success_rate'] = pattern_data['correct_predictions'] / pattern_data['total_occurrences']
        pattern_data['last_seen'] = datetime.now().isoformat()
        pattern_data['prediction_history'].append({
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat()
        })
        
        if len(pattern_data['prediction_history']) > 50:
            pattern_data['prediction_history'] = pattern_data['prediction_history'][-50:]
        
        self.ai_total_predictions += 1
        if was_correct:
            self.ai_correct_predictions += 1
        
        self.ai_accuracy = self.ai_correct_predictions / self.ai_total_predictions if self.ai_total_predictions > 0 else 0
        
        self.pattern_history.append({
            'pattern_hash': pattern_hash,
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat(),
            'ai_confidence': getattr(self, 'last_ai_confidence', 0.5)
        })
        
        if len(self.pattern_history) > 1000:
            self.pattern_history = self.pattern_history[-1000:]
        
        if self.ai_total_predictions % 50 == 0:
            self.retrain_ai_model()

    def retrain_ai_model(self):
        if len(self.pattern_history) < self.min_training_samples:
            return
        
        try:
            logging.info(f"🔄 Retraining AI model with {len(self.pattern_history)} samples...")
            
            X_train = []
            y_train = []
            
            for pattern_data in self.pattern_history:
                if 'features' in pattern_data:
                    X_train.append(pattern_data['features'])
                    y_train.append(1 if pattern_data['was_correct'] else 0)
            
            if len(X_train) < self.min_training_samples:
                return
            
            X_train_array = np.array(X_train)
            y_train_array = np.array(y_train)
            
            self.scaler.fit(X_train_array)
            X_train_scaled = self.scaler.transform(X_train_array)
            
            self.ai_model.fit(X_train_scaled, y_train_array)
            
            self.ai_learning_cycles += 1
            logging.info(f"✅ AI Model retrained. Learning cycle: {self.ai_learning_cycles}")
            self.save_ai_model()
            
        except Exception as e:
            logging.error(f"❌ Error retraining AI model: {e}")

    def predict_with_ai(self, results, numbers):
        try:
            if len(results) < self.pattern_window_size:
                return None, 0.5
            
            features = self.extract_features_for_ai(results, numbers)
            
            if len(features) < self.feature_count:
                return None, 0.5
            
            features_array = np.array([features])
            
            if hasattr(self.scaler, 'scale_'):
                features_scaled = self.scaler.transform(features_array)
            else:
                features_scaled = features_array
            
            if hasattr(self.ai_model, 'predict_proba'):
                proba = self.ai_model.predict_proba(features_scaled)[0]
                prediction_proba = max(proba)
                prediction_class = self.ai_model.predict(features_scaled)[0]
            else:
                return None, 0.5
            
            prediction = 'BIG' if prediction_class == 1 else 'SMALL'
            
            result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
            pattern_hash = self.calculate_pattern_hash(result_numeric)
            
            self.last_ai_pattern_used = {
                'pattern_hash': pattern_hash,
                'prediction': prediction,
                'confidence': float(prediction_proba),
                'features': features
            }
            
            return prediction, float(prediction_proba)
            
        except Exception as e:
            logging.error(f"❌ AI Prediction error: {e}")
            return None, 0.5

    def analyze_pattern_with_ai(self, data_list):
        if not data_list or len(data_list) < 10:
            return random.choice(['BIG', 'SMALL']), 50
        
        recent_data = data_list[:50]
        results = [item['big_small'] for item in recent_data]
        numbers = [item['number'] for item in recent_data]
        
        ai_prediction, ai_confidence = self.predict_with_ai(results, numbers)
        
        patterns = self.detect_winning_patterns(results, numbers)
        strategies = self.calculate_winning_strategies(patterns)
        trad_prediction, trad_confidence = self.combine_winning_strategies(strategies)
        
        final_prediction = None
        final_confidence = 0
        
        if ai_prediction and ai_confidence > self.ai_confidence_threshold:
            final_prediction = ai_prediction
            final_confidence = ai_confidence * 100
            
            if self.ai_accuracy > 0.7:
                self.pattern_weights['ai_pattern'] = 0.55
            else:
                self.pattern_weights['ai_pattern'] = 0.45
                
        else:
            final_prediction = trad_prediction
            final_confidence = trad_confidence
        
        recent10 = results[:10]
        big_count = sum(1 for r in recent10 if r == 'BIG')
        small_count = sum(1 for r in recent10 if r == 'SMALL')
        dominant = 'BIG' if big_count >= 8 else ('SMALL' if small_count >= 8 else None)

        recent4 = results[:4]
        r4_big = sum(1 for r in recent4 if r == 'BIG')
        r4_small = sum(1 for r in recent4 if r == 'SMALL')
        short_bias = 'BIG' if r4_big >= 3 else ('SMALL' if r4_small >= 3 else None)

        if dominant and final_prediction != dominant:
            final_prediction = dominant
            final_confidence = max(final_confidence, 68)
        elif short_bias and final_prediction != short_bias:
            final_prediction = short_bias
            final_confidence = max(final_confidence, 66)

        if self.consecutive_losses >= 2 and not dominant and not short_bias:
            final_prediction = 'BIG' if final_prediction == 'SMALL' else 'SMALL'
            final_confidence = max(final_confidence, 70)

        recent_predictions = list(self.big_small_history)
        if len(recent_predictions) >= 6 and not dominant and not short_bias:
            recent_predictions = recent_predictions[-6:]
            if all(p == final_prediction for p in recent_predictions):
                final_prediction = 'BIG' if final_prediction == 'SMALL' else 'SMALL'
                final_confidence = max(60, final_confidence - 10)

        self.big_small_history.append(final_prediction)
        
        self.last_ai_confidence = ai_confidence if ai_prediction else 0
        
        return final_prediction, final_confidence

    def detect_winning_patterns(self, results, numbers):
        patterns = {}
        
        if len(results) < 10:
            return patterns
        
        current_streak = 1
        current_type = results[0]
        for i in range(1, len(results)):
            if results[i] == current_type:
                current_streak += 1
            else:
                break
        patterns['current_streak'] = current_streak
        patterns['streak_type'] = current_type
        
        last_20_results = results[:20]
        big_count_20 = last_20_results.count('BIG')
        small_count_20 = last_20_results.count('SMALL')
        
        patterns['big_20'] = big_count_20
        patterns['small_20'] = small_count_20
        patterns['imbalance_20'] = big_count_20 - small_count_20
        
        gap_big = 0
        gap_small = 0
        for i, r in enumerate(results[:10]):
            if r == 'BIG':
                gap_big = i
                break
        else:
            gap_big = 10
        
        for i, r in enumerate(results[:10]):
            if r == 'SMALL':
                gap_small = i
                break
        else:
            gap_small = 10
            
        patterns['gap_big'] = gap_big
        patterns['gap_small'] = gap_small
        
        if numbers and len(numbers) >= 15:
            recent_numbers = numbers[:15]
            big_nums = sum(1 for n in recent_numbers if n >= 5)
            small_nums = sum(1 for n in recent_numbers if n <= 4)
            patterns['big_nums_15'] = big_nums
            patterns['small_nums_15'] = small_nums
            patterns['number_imbalance'] = big_nums - small_nums
            
            number_counter = Counter(recent_numbers)
            hot_numbers = [num for num, count in number_counter.items() if count >= 2]
            cold_numbers = [num for num in range(10) if num not in recent_numbers[-5:]]
            
            patterns['hot_numbers'] = hot_numbers
            patterns['cold_numbers'] = cold_numbers
            patterns['hot_big'] = sum(1 for n in hot_numbers if n >= 5)
            patterns['hot_small'] = sum(1 for n in hot_numbers if n <= 4)
            
            recent_5 = numbers[:5]
            recent_trend_big = sum(1 for n in recent_5 if n >= 5)
            recent_trend_small = sum(1 for n in recent_5 if n <= 4)
            patterns['recent_trend'] = 'BIG' if recent_trend_big > recent_trend_small else 'SMALL'
        
        alternating_score = 0
        for i in range(2, min(10, len(results))):
            if results[i] != results[i-1]:
                alternating_score += 1
        patterns['alternating_score'] = alternating_score / 8.0
        
        consecutive_same = 0
        last_result = results[0]
        for result in results[:8]:
            if result == last_result:
                consecutive_same += 1
            else:
                break
        patterns['consecutive_same'] = consecutive_same
        
        return patterns

    def calculate_winning_strategies(self, patterns):
        strategies = []
        
        if patterns.get('current_streak', 0) >= 2:
            if patterns['current_streak'] >= 3:
                prediction = 'BIG' if patterns['streak_type'] == 'SMALL' else 'SMALL'
                confidence = min(90, 70 + (patterns['current_streak'] - 2) * 10)
                strategies.append(('streak_breaker_long', prediction, confidence))
            elif patterns['current_streak'] == 2:
                if random.random() < 0.4:
                    prediction = patterns['streak_type']
                    confidence = 65
                    strategies.append(('streak_continue', prediction, confidence))
                else:
                    prediction = 'BIG' if patterns['streak_type'] == 'SMALL' else 'SMALL'
                    confidence = 70
                    strategies.append(('streak_breaker_short', prediction, confidence))
        
        imbalance = patterns.get('imbalance_20', 0)
        if abs(imbalance) >= 3:
            if imbalance > 0:
                prediction = 'SMALL'
                confidence = min(85, 70 + abs(imbalance) * 3)
            else:
                prediction = 'BIG'
                confidence = min(85, 70 + abs(imbalance) * 3)
            strategies.append(('balance_correction', prediction, confidence))
        
        gap_diff = patterns.get('gap_big', 0) - patterns.get('gap_small', 0)
        if abs(gap_diff) >= 3:
            if gap_diff > 0:
                prediction = 'BIG'
                confidence = 75 + min(15, gap_diff * 3)
            else:
                prediction = 'SMALL'
                confidence = 75 + min(15, abs(gap_diff) * 3)
            strategies.append(('gap_filling', prediction, confidence))
        
        number_imbalance = patterns.get('number_imbalance', 0)
        if abs(number_imbalance) >= 4:
            if number_imbalance > 0:
                prediction = 'SMALL'
                confidence = 70 + min(20, number_imbalance * 2)
            else:
                prediction = 'BIG'
                confidence = 70 + min(20, abs(number_imbalance) * 2)
            strategies.append(('number_pattern_correction', prediction, confidence))
        
        if 'recent_trend' in patterns:
            recent_trend = patterns['recent_trend']
            if patterns.get('consecutive_same', 0) < 3:
                prediction = recent_trend
                confidence = 65
                strategies.append(('trend_following', prediction, confidence))
        
        if random.random() < 0.2:
            prediction = random.choice(['BIG', 'SMALL'])
            confidence = 55
            strategies.append(('random_walk', prediction, confidence))
        
        if patterns.get('hot_big', 0) > patterns.get('hot_small', 0) + 2:
            prediction = 'BIG'
            confidence = 70
            strategies.append(('hot_number_big', prediction, confidence))
        elif patterns.get('hot_small', 0) > patterns.get('hot_big', 0) + 2:
            prediction = 'SMALL'
            confidence = 70
            strategies.append(('hot_number_small', prediction, confidence))
        
        if patterns.get('alternating_score', 0) > 0.7:
            last_result = self.last_actual_results[0] if self.last_actual_results else None
            if last_result:
                prediction = 'BIG' if last_result == 'SMALL' else 'SMALL'
                confidence = 70
                strategies.append(('alternating_pattern', prediction, confidence))
        
        return strategies

    def combine_winning_strategies(self, strategies):
        if not strategies:
            return random.choice(['BIG', 'SMALL']), 50
        
        big_score = 0
        small_score = 0
        
        for strategy_name, prediction, confidence in strategies:
            weight = self.pattern_weights.get(strategy_name, 0.1)
            strategy_success = self.strategy_success_count.get(strategy_name, 0.5)
            adjusted_weight = weight * (0.5 + strategy_success)
            
            score = confidence * adjusted_weight
            
            if prediction == 'BIG':
                big_score += score
            else:
                small_score += score
        
        if self.consecutive_losses >= 2:
            if self.consecutive_losses >= 3:
                if big_score > small_score:
                    return 'SMALL', min(80, small_score + 20)
                else:
                    return 'BIG', min(80, big_score + 20)
        
        if big_score > small_score:
            final_confidence = min(95, big_score)
            return 'BIG', final_confidence
        else:
            final_confidence = min(95, small_score)
            return 'SMALL', final_confidence

    def analyze_pattern_advanced(self, data_list):
        return self.analyze_pattern_with_ai(data_list)

    def format_single_prediction(self, channel_id, period, prediction, for_channel=False):
        channel_config = self.get_channel_config(channel_id)
        template = self.get_channel_template(channel_id, 'single_prediction')
        
        if prediction == 'BIG':
            prediction_text = "𝘽𝙄𝙂𝙂"
        else:
            prediction_text = "𝘚𝙈𝘼𝙇𝙇"
        
        period_str = str(period)
        if len(period_str) >= 4:
            period_display = period_str[-4:]
        else:
            period_display = period_str.zfill(4)
        
        period_text = f"➤ {period_display}  ➜  {prediction_text}"
        
        format_dict = {
            'register_link': channel_config['register_link'],
            'period': period_text,
            'prediction': prediction_text,
            'crown': self.get_emoji('crown', for_channel),
            'link': self.get_emoji('link', for_channel),
            'fire': self.get_emoji('fire', for_channel),
            'sparkles': self.get_emoji('sparkles', for_channel),
            'rocket': self.get_emoji('rocket', for_channel),
            'money': self.get_emoji('money', for_channel),
            'check': self.get_emoji('check', for_channel),
            'chart': self.get_emoji('chart', for_channel),
            'target': self.get_emoji('target', for_channel),
            'trophy': self.get_emoji('trophy', for_channel),
            'gift': self.get_emoji('gift', for_channel),
            'lightning': self.get_emoji('lightning', for_channel),
            'star': self.get_emoji('star', for_channel),
            'warning': self.get_emoji('warning', for_channel),
            'clock': self.get_emoji('clock', for_channel),
            'moon': self.get_emoji('moon', for_channel),
            'sun': self.get_emoji('sun', for_channel),
            'coffee': self.get_emoji('coffee', for_channel),
            'sleep': self.get_emoji('sleep', for_channel),
            'break_icon': self.get_emoji('break_icon', for_channel),
            'reload': self.get_emoji('reload', for_channel),
            'party': self.get_emoji('party', for_channel),
            'money_loss': self.get_emoji('money_loss', for_channel),
            'star2': self.get_emoji('star2', for_channel)
        }
        
        for emoji_key in self.emoji_config.get('premium_emojis', {}).keys():
            if emoji_key not in format_dict:
                format_dict[emoji_key] = self.get_emoji(emoji_key, for_channel)

        formatted_text = template
        for k, v in format_dict.items():
            formatted_text = formatted_text.replace(f"{{{k}}}", str(v))
        
        formatted_text = self.format_with_emojis(formatted_text, for_channel)
        
        return formatted_text

    async def ensure_bot_channel_access(self, context: ContextTypes.DEFAULT_TYPE, channel_id):
        try:
            me = await context.bot.get_me()
            member = await context.bot.get_chat_member(channel_id, me.id)
            status = getattr(member, 'status', '')
            if str(status).lower() in ('left', 'kicked', 'banned'):
                raise Exception(f"bot status={status}")
            return True
        except Exception as e:
            logging.warning(f"⚠️ Channel access check failed for {channel_id}. Keeping channel in config. Error: {e}")
            return False

    async def send_single_prediction(self, context: ContextTypes.DEFAULT_TYPE, channel_id, period, prediction):
        if not await self.ensure_bot_channel_access(context, channel_id):
            return False

        use_premium = self.use_user_account
        
        message_text = self.format_single_prediction(channel_id, period, prediction, for_channel=use_premium)
        
        result = await self.send_message_with_retry(
            context=context,
            chat_id=channel_id,
            text=message_text,
            for_channel=use_premium
        )
        
        if result:
            msg_id = self._extract_message_id(result)
            if msg_id:
                if channel_id not in self.prediction_message_ids:
                    self.prediction_message_ids[channel_id] = {}
                self.prediction_message_ids[channel_id][period] = msg_id
        else:
            logging.error(f"❌ Failed to send prediction to {channel_id}")
        
        return result

    async def send_event_message(self, context: ContextTypes.DEFAULT_TYPE, channel_id, event_type, **kwargs):
        event_type = self.normalize_event_type(event_type)

        custom_messages = self.get_custom_messages(channel_id, event_type)
        use_custom = custom_messages and len(custom_messages) > 0

        media_items = self.get_event_media(channel_id, event_type)
        
        # FIXED: Send win/loss media first when result occurs
        if event_type in ['win', 'loss'] and media_items:
            logging.info(f"📸 Sending {event_type} media to {channel_id}")
            await self.send_media_group(context, channel_id, media_items)
            return True

        media_first_events = {'break', 'session_start'}
        if media_items and event_type in media_first_events:
            await self.send_media_group(context, channel_id, media_items)

        if use_custom:
            for message_data in custom_messages:
                await self.send_stored_message(
                    context, channel_id, message_data,
                    session=kwargs.get('session', ''),
                    next_session=kwargs.get('next_session', ''),
                    wins=kwargs.get('wins', 0),
                    losses=kwargs.get('losses', 0),
                    win_rate=kwargs.get('win_rate', 0),
                    break_duration=kwargs.get('break_duration', self.custom_break_duration)
                )
            if media_items and event_type not in media_first_events:
                await self.send_media_group(context, channel_id, media_items)
            return True

        template_key = {
            'session_start': 'new_session',
            'break': 'break_message',
            'good_morning': 'good_morning',
            'good_night': 'good_night'
        }.get(event_type)
        
        if not template_key:
            return False
        
        template = self.get_channel_template(channel_id, template_key)
        channel_config = self.get_channel_config(channel_id)
        
        format_dict = {
            'session': kwargs.get('session', ''),
            'next_session': kwargs.get('next_session', ''),
            'wins': kwargs.get('wins', 0),
            'losses': kwargs.get('losses', 0),
            'win_rate': kwargs.get('win_rate', 0),
            'break_duration': kwargs.get('break_duration', self.custom_break_duration),
            'register_link': channel_config['register_link'],
            'promo_text': channel_config['promotional_text'] if channel_config['show_promo'] else '',
            'crown': self.get_emoji('crown', True),
            'sparkles': self.get_emoji('sparkles', True),
            'check': self.get_emoji('check', True),
            'chart': self.get_emoji('chart', True),
            'link': self.get_emoji('link', True),
            'sun': self.get_emoji('sun', True),
            'moon': self.get_emoji('moon', True),
            'sleep': self.get_emoji('sleep', True),
            'clock': self.get_emoji('clock', True),
            'reload': self.get_emoji('reload', True),
            'rocket': self.get_emoji('rocket', True),
            'break_icon': self.get_emoji('break_icon', True),
            'target': self.get_emoji('target', True),
            'trophy': self.get_emoji('trophy', True),
            'fire': self.get_emoji('fire', True),
            'money': self.get_emoji('money', True),
            'lightning': self.get_emoji('lightning', True),
            'coffee': self.get_emoji('coffee', True),
            'gift': self.get_emoji('gift', True)
        }
        
        try:
            formatted_text = template.format(**format_dict)
        except KeyError as e:
            logging.warning(f"⚠️ KeyError in template: {e}")
            formatted_text = template
        
        formatted_text = self.format_with_emojis(formatted_text, for_channel=True)
        
        if not formatted_text or not formatted_text.strip():
            fallback_template = self.default_templates.get(template_key, '')
            try:
                formatted_text = fallback_template.format(**format_dict) if fallback_template else ''
            except KeyError:
                formatted_text = fallback_template
            formatted_text = self.format_with_emojis(formatted_text, for_channel=True) if formatted_text else ''
        
        if not formatted_text or not formatted_text.strip():
            formatted_text = f"{event_type.replace('_', ' ').title()} update"
        
        await self.send_message_with_retry(
            context=context,
            chat_id=channel_id,
            text=formatted_text,
            for_channel=True
        )
        
        if media_items and event_type not in media_first_events:
            await self.send_media_group(context, channel_id, media_items)

        return True

    async def send_stored_message(self, context: ContextTypes.DEFAULT_TYPE, channel_id, message_data, **placeholders):
        media_items = message_data.get('media_group', [])
        text_content = message_data.get('text', '')
        send_order = message_data.get('send_order', 'text_first')
        
        use_user_account = self.use_user_account
        
        if text_content:
            text_content = self.format_placeholders(text_content, channel_id, **placeholders)
            formatted_text = self.format_custom_message_with_premium_emojis(text_content, channel_id)
        else:
            formatted_text = None
        
        if media_items:
            src_chat = message_data.get('source_chat_id')
            src_msg = message_data.get('source_message_id')
            if not (src_chat and src_msg):
                for _m in media_items:
                    if _m.get('source_chat_id') and _m.get('source_message_id'):
                        src_chat = _m.get('source_chat_id')
                        src_msg = _m.get('source_message_id')
                        break

            first_item = media_items[0] if media_items else {}
            first_name = str(first_item.get('file_name', '') or '').lower()
            is_binary_doc = first_name.endswith(('.apk', '.exe', '.zip', '.rar', '.pdf', '.html', '.htm', '.txt', '.doc', '.docx', '.xls', '.xlsx', '.bin'))
            if len(media_items) == 1 and src_chat and src_msg and is_binary_doc:
                try:
                    await context.bot.copy_message(chat_id=channel_id, from_chat_id=src_chat, message_id=src_msg)
                    if formatted_text and send_order in ('text_first', 'media_first'):
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            text=formatted_text,
                            for_channel=use_user_account
                        )
                    return
                except Exception as e:
                    logging.warning(f"⚠️ copy_message fallback failed: {e}")

        if send_order == 'combined' and media_items:
            formatted_media_group = []
            for i, media_item in enumerate(media_items):
                media_type = media_item.get('type', 'photo')
                file_id = media_item.get('file_id')
                
                if file_id:
                    caption = formatted_text if (formatted_text and i == 0) else None
                    formatted_media_group.append({
                        'type': media_type,
                        'media': file_id,
                        'caption': caption,
                        'file_name': media_item.get('file_name')
                    })
            
            if formatted_media_group:
                send_via_user = bool(formatted_text)
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    for_channel=send_via_user,
                    media_group=formatted_media_group
                )
                
        elif send_order == 'text_first':
            if formatted_text:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    text=formatted_text,
                    for_channel=use_user_account
                )
            
            if media_items:
                if len(media_items) > 1:
                    formatted_media_group = []
                    for media_item in media_items:
                        media_type = media_item.get('type', 'photo')
                        file_name = str(media_item.get('file_name','')).lower()
                        if not file_name:
                            actual_type = media_type
                        else:
                            _, actual_type = self.detect_media_type_from_file(file_name)
                        file_id = media_item.get('file_id')
                        
                        if file_id:
                            formatted_media_group.append({
                                'type': actual_type,
                                'media': file_id,
                                'caption': None,
                                'file_name': media_item.get('file_name')
                            })
                    
                    if formatted_media_group:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_group=formatted_media_group
                        )
                else:
                    media_item = media_items[0]
                    media_type = media_item.get('type', 'photo')
                    file_name = str(media_item.get('file_name','')).lower()
                    if not file_name:
                        actual_type = media_type
                    else:
                        _, actual_type = self.detect_media_type_from_file(file_name)
                    file_id = media_item.get('file_id')
                    
                    if file_id:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_type=actual_type,
                            media_file=file_id,
                            filename_hint=media_item.get('file_name')
                        )
                        
        elif send_order == 'media_first':
            if media_items:
                if len(media_items) > 1:
                    formatted_media_group = []
                    for media_item in media_items:
                        media_type = media_item.get('type', 'photo')
                        file_name = str(media_item.get('file_name','')).lower()
                        if not file_name:
                            actual_type = media_type
                        else:
                            _, actual_type = self.detect_media_type_from_file(file_name)
                        file_id = media_item.get('file_id')
                        
                        if file_id:
                            formatted_media_group.append({
                                'type': actual_type,
                                'media': file_id,
                                'caption': None,
                                'file_name': media_item.get('file_name')
                            })
                    
                    if formatted_media_group:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_group=formatted_media_group
                        )
                else:
                    media_item = media_items[0]
                    media_type = media_item.get('type', 'photo')
                    file_name = str(media_item.get('file_name','')).lower()
                    if not file_name:
                        actual_type = media_type
                    else:
                        _, actual_type = self.detect_media_type_from_file(file_name)
                    file_id = media_item.get('file_id')
                    
                    if file_id:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_type=actual_type,
                            media_file=file_id,
                            filename_hint=media_item.get('file_name')
                        )
            
            if formatted_text:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    text=formatted_text,
                    for_channel=use_user_account
                )

    async def send_media_group(self, context: ContextTypes.DEFAULT_TYPE, channel_id, media_items):
        if not media_items:
            return

        # Prefer copy_message when source reference exists; avoids broken/expired file_id issues
        copied_any = False
        copy_failed = False
        for item in media_items:
            src_chat = item.get('source_chat_id')
            src_msg = item.get('source_message_id')
            if src_chat and src_msg:
                try:
                    await context.bot.copy_message(chat_id=channel_id, from_chat_id=src_chat, message_id=src_msg)
                    copied_any = True
                except Exception as e:
                    copy_failed = True
                    logging.warning(f"⚠️ copy_message failed for {channel_id}: {e}")
            else:
                copy_failed = True

        if copied_any and not copy_failed:
            logging.info(f"✅ Media copied successfully to {channel_id}")
            return
            
        if len(media_items) > 1:
            formatted_media_group = []
            for i, media_item in enumerate(media_items):
                mtype = media_item.get('type', 'photo')
                file_name = str(media_item.get('file_name','')).lower()
                detected_type, actual_type = self.detect_media_type_from_file(file_name)
                fid = media_item.get('file_id')
                if not fid:
                    continue
                if actual_type == 'sticker':
                    await self.send_message_with_retry(
                        context=context,
                        chat_id=channel_id,
                        for_channel=self.use_user_account,
                        media_type='sticker',
                        media_file=fid
                    )
                    continue
                formatted_media_group.append({
                    'type': actual_type,
                    'media': fid,
                    'caption': None,
                    'file_name': media_item.get('file_name')
                })
            
            if formatted_media_group:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    for_channel=self.use_user_account,
                    media_group=formatted_media_group
                )
        else:
            media_item = media_items[0]
            file_name = str(media_item.get('file_name','')).lower()
            detected_type, actual_type = self.detect_media_type_from_file(file_name)
            await self.send_message_with_retry(
                context=context,
                chat_id=channel_id,
                for_channel=self.use_user_account,
                media_type=actual_type,
                media_file=media_item.get('file_id'),
                filename_hint=media_item.get('file_name')
            )

    async def send_result_media(self, context: ContextTypes.DEFAULT_TYPE, channel_id, result_type):
        """Send win/loss result media"""
        media_items = self.get_event_media(channel_id, result_type)
        if media_items:
            logging.info(f"📸 Sending {result_type} media to {channel_id}")
            await self.send_media_group(context, channel_id, media_items)
        else:
            logging.warning(f"⚠️ No media found for {result_type} on {channel_id}")

    async def check_result_and_send_next(self, context: ContextTypes.DEFAULT_TYPE, data):
        if not self.current_prediction_period or not self.waiting_for_result:
            return False
        
        result_found = False
        for item in data[:10]:
            if item['issueNumber'] == self.current_prediction_period:
                result = item['big_small']
                is_win = self.current_prediction_choice == result
                
                results = [item['big_small'] for item in data[:20]]
                numbers = [item['number'] for item in data[:20]]
                
                result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
                if len(result_numeric) >= self.pattern_window_size:
                    pattern_hash = self.calculate_pattern_hash(result_numeric)
                    
                    self.learn_from_pattern(pattern_hash, self.current_prediction_choice, is_win)
                    
                    self.ai_prediction_history.append({
                        'prediction': self.current_prediction_choice,
                        'result': result,
                        'was_correct': is_win,
                        'pattern_hash': pattern_hash,
                        'timestamp': datetime.now().isoformat()
                    })
                
                if is_win:
                    self.session_wins += 1
                    self.consecutive_wins += 1
                    self.consecutive_losses = 0
                    self.last_prediction_was_loss = False
                    self.last_result_was_win = True
                    
                    if hasattr(self, 'last_strategy'):
                        self.strategy_success_count[self.last_strategy] = self.strategy_success_count.get(self.last_strategy, 0) + 1
                    
                    target_channels = self.current_active_prediction_channels or self.active_channels
                    for channel in target_channels:
                        if not self.is_channel_prediction_active(channel):
                            continue
                        # FIXED: Send win media immediately
                        await self.send_result_media(context, channel, 'win')
                        logging.info(f"✅ Win media sent to {channel}")
                else:
                    self.session_losses += 1
                    self.consecutive_losses += 1
                    self.consecutive_wins = 0
                    self.last_prediction_was_loss = True
                    self.last_result_was_win = False
                    
                    if hasattr(self, 'last_strategy'):
                        self.strategy_success_count[self.last_strategy] = max(0, self.strategy_success_count.get(self.last_strategy, 0.5) - 0.1)
                    
                    target_channels = self.current_active_prediction_channels or self.active_channels
                    for channel in target_channels:
                        if not self.is_channel_prediction_active(channel):
                            continue
                        # FIXED: Send loss media immediately
                        await self.send_result_media(context, channel, 'loss')
                        logging.info(f"❌ Loss media sent to {channel}")

                target_channels = self.current_active_prediction_channels or self.active_channels
                for channel in target_channels:
                    if not self.is_channel_prediction_active(channel):
                        continue
                    msg_id = self.prediction_message_ids.get(channel, {}).pop(self.current_prediction_period, None)
                    if not msg_id:
                        continue

                    if channel not in self.cycle_prediction_ids:
                        self.cycle_prediction_ids[channel] = []
                    if msg_id not in self.cycle_prediction_ids[channel]:
                        self.cycle_prediction_ids[channel].append(msg_id)

                    if is_win:
                        while len(self.cycle_prediction_ids[channel]) > self.max_loss_predictions_keep:
                            old_id = self.cycle_prediction_ids[channel].pop(0)
                            await self.delete_channel_message(context, channel, old_id)

                        self.cycle_prediction_ids[channel] = []
                
                result_found = True
                break
        
        if result_found:
            if self.pending_break and self.last_result_was_win:
                next_session_display = self.pending_break_next_session or ""
                await self.send_break_message(context, next_session_display)
                self.in_break_period = True
                self.break_message_sent = True
                self.session_ended = True
                self.waiting_for_win = False
                self.waiting_for_result = False
                self.current_prediction_period = None
                self.current_prediction_choice = None
                self.pending_break = False
                self.pending_break_next_session = None
                return True

            latest = data[0]
            latest_period = latest.get('issueNumber')
            next_period = self.get_next_period(latest_period)
            
            choice, confidence = self.analyze_pattern_advanced(data)
            
            self.current_prediction_period = next_period
            self.current_prediction_choice = choice
            self.waiting_for_result = True
            
            target_channels = self.current_active_prediction_channels or self.active_channels
            for channel in target_channels:
                if self.pending_break or self.is_channel_prediction_active(channel):
                    await self.send_single_prediction(context, channel, next_period, choice)
            
            return True
        
        return False

    async def send_first_prediction(self, context: ContextTypes.DEFAULT_TYPE, data):
        if self.waiting_for_result:
            return False
        
        latest = data[0]
        latest_period = latest.get('issueNumber')
        next_period = self.get_next_period(latest_period)
        
        choice, confidence = self.analyze_pattern_advanced(data)
        
        self.current_prediction_period = next_period
        self.current_prediction_choice = choice
        self.waiting_for_result = True
        
        target_channels = self.current_active_prediction_channels or self.active_channels
        for channel in target_channels:
            if self.pending_break or self.is_channel_prediction_active(channel):
                await self.send_single_prediction(context, channel, next_period, choice)
        
        return True

    async def send_new_session_message(self, context: ContextTypes.DEFAULT_TYPE, channel_id=None):
        """Send session start message for specific channel or all channels"""
        channels_to_send = [channel_id] if channel_id else self.active_channels
        
        for channel in channels_to_send:
            try:
                if not self.is_channel_prediction_active(channel):
                    continue
                
                next_session = self.get_next_session_time_for_channel(channel)
                session_display = self.format_session_time_range(next_session, next_session)
                
                await self.send_event_message(
                    context, channel, 'session_start',
                    session=session_display
                )
                
                logging.info(f"✅ Session start message sent to {channel}: {session_display}")
                
            except Exception as e:
                logging.error(f"❌ Failed to send new session message to {channel}: {e}")

    async def send_good_morning_message(self, context: ContextTypes.DEFAULT_TYPE):
        self.morning_message_sent = True
        self.night_message_sent = False
        
        self.session_ended = False
        self.in_break_period = False
        self.break_message_sent = False
        self.waiting_for_result = False
        self.last_result_was_win = False
        self.waiting_for_win = False
        self.session_start_sent = False
        
        self.session_wins = 0
        self.session_losses = 0
        self.consecutive_losses = 0
        self.consecutive_wins = 0
        self.big_small_history.clear()
        
        if not self.active_channels:
            return
        
        success_count = 0
        for channel in self.active_channels:
            try:
                await self.send_event_message(context, channel, 'good_morning')
                success_count += 1
                
            except Exception as e:
                logging.error(f"❌ Failed to send morning message to {channel}: {e}")
        
        logging.info(f"✅ Morning messages sent: {success_count}/{len(self.active_channels)}")

    async def send_good_night_message(self, context: ContextTypes.DEFAULT_TYPE):
        self.night_message_sent = True
        self.morning_message_sent = False
        self.in_break_period = True
        self.break_message_sent = True

        total_predictions = self.session_wins + self.session_losses
        win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0

        if not self.active_channels:
            return

        success_count = 0
        next_session = "10:00 AM"

        for channel in self.active_channels:
            try:
                if not self.is_channel_prediction_active(channel):
                    continue

                await self.send_event_message(
                    context, channel, 'break',
                    next_session=next_session,
                    break_duration=self.custom_break_duration
                )

                channel_config = self.get_channel_config(channel)
                if channel_config.get('custom_break_enabled', False):
                    multi_break = self.get_custom_break_messages(channel)
                    for msg in multi_break:
                        await self.send_stored_message(context, channel, msg)

                await self.send_event_message(
                    context, channel, 'good_night',
                    wins=self.session_wins,
                    losses=self.session_losses,
                    win_rate=win_rate
                )
                success_count += 1

            except Exception as e:
                logging.error(f"❌ Failed night flow for {channel}: {e}")

        for channel in self.active_channels:
            if not self.is_channel_prediction_active(channel):
                continue
            custom_messages = self.get_custom_messages(channel, 'good_night')
            if custom_messages:
                for message_data in custom_messages:
                    await self.send_stored_message(context, channel, message_data)

        logging.info(f"✅ Night messages sent: {success_count}/{len(self.active_channels)}")

    async def send_break_message_for_channel(self, context: ContextTypes.DEFAULT_TYPE, channel, next_session):
        try:
            if not self.is_channel_enabled(channel):
                return False
            channel_next_session = self.get_next_session_time_for_channel(channel)
            await self.send_event_message(
                context, channel, 'break',
                next_session=channel_next_session or next_session,
                break_duration=self.custom_break_duration
            )

            channel_config = self.get_channel_config(channel)
            if channel_config.get('custom_break_enabled', False):
                messages = self.get_custom_break_messages(channel)
                if messages:
                    delay_minutes = channel_config.get('custom_break_delay', 5)
                    for message_index, message_data in enumerate(messages):
                        message_delay = (delay_minutes * 60) + (message_index * 60)
                        task = asyncio.create_task(
                            self.send_custom_break_message_delayed(
                                context, channel, message_index, message_delay
                            )
                        )
                        task_key = f"{channel}:{message_index}"
                        self.scheduled_tasks[task_key] = task
            return True
        except Exception as e:
            logging.error(f"❌ Exception sending break message to {channel}: {e}")
            return False

    async def send_break_message(self, context: ContextTypes.DEFAULT_TYPE, next_session):
        await self.cancel_scheduled_tasks()
        
        self.sent_custom_messages_in_break = {}
        self.break_start_time = datetime.now()
        
        if not self.active_channels:
            return
        
        success_count = 0
        for channel in self.active_channels:
            try:
                if not self.is_channel_enabled(channel):
                    continue

                channel_next_session = self.get_next_session_time_for_channel(channel)
                
                await self.send_event_message(
                    context, channel, 'break',
                    next_session=channel_next_session,
                    break_duration=self.custom_break_duration
                )
                success_count += 1
                
                channel_config = self.get_channel_config(channel)
                if channel_config.get('custom_break_enabled', False):
                    messages = self.get_custom_break_messages(channel)
                    if messages:
                        delay_minutes = channel_config.get('custom_break_delay', 5)
                        
                        for message_index, message_data in enumerate(messages):
                            message_delay = (delay_minutes * 60) + (message_index * 60)
                            task = asyncio.create_task(
                                self.send_custom_break_message_delayed(
                                    context, channel, message_index, message_delay
                                )
                            )
                            
                            task_key = f"{channel}:{message_index}"
                            self.scheduled_tasks[task_key] = task
                            
            except Exception as e:
                logging.error(f"❌ Exception sending break message to {channel}: {e}")
        
        logging.info(f"✅ Break messages sent: {success_count}/{len(self.active_channels)}")

    async def cancel_scheduled_tasks(self):
        try:
            for task_key, task in list(self.scheduled_tasks.items()):
                if not task.done():
                    task.cancel()
            self.scheduled_tasks.clear()
        except Exception as e:
            logging.error(f"❌ Error cancelling tasks: {e}")

    async def send_custom_break_message_delayed(self, context: ContextTypes.DEFAULT_TYPE, channel_id, message_index, delay_seconds):
        try:
            await asyncio.sleep(delay_seconds)
            
            if not self.is_channel_enabled(channel_id):
                return
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                return
            
            await self.send_stored_message(context, channel_id, message_data)
            
        except asyncio.CancelledError:
            pass
        except Exception as e:
            logging.error(f"❌ Error in delayed custom break message for {channel_id}: {e}")

    # ==================== Command Handlers ====================
    async def start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user.id not in self.config['admin_ids']:
            await update.message.reply_text("Access denied contact admin @aviii56")
            return
            
        await update.message.reply_text(
            "🤖 WinGo Bot Admin Panel\n\n"
            "🎯 REAL AI PATTERN RECOGNITION\n"
            "• GPT-4/Claude like pattern learning\n"
            "• Win Rate: 80-85%+ target\n"
            "• Learns from every result\n\n"
            "🎨 Multiple Custom Break Messages\n"
            "📝 Event Media System\n"
            "🎯 Custom Messages for Every Event\n"
            "⏱️ Adjustable Break Duration\n"
            "⏯️ Per-Channel Prediction Control\n"
            "⏰ Channel-Specific Time Windows (NEW!)\n"
            "📎 Supports ANY file type\n"
            "🎨 Stickers, GIFs, Photos, Videos, Documents\n\n"
            "✅ Session start messages sent 5 minutes before each session!\n"
            "✅ Win/Loss media now sends immediately!\n"
            "Select an option below:",
            reply_markup=self.get_keyboard('main')
        )

    async def handle_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        await query.answer()
        
        if query.from_user.id not in self.config['admin_ids']:
            await query.edit_message_text("Not authorized")
            return
            
        data = query.data
        chat_id = query.message.chat_id
        
        try:
            if data == 'noop':
                await query.answer()
                return

            elif data == 'main_menu':
                await query.edit_message_text(
                    "🤖 WinGo Bot Admin Panel\n\n"
                    "🎯 REAL AI PATTERN RECOGNITION\n"
                    "• GPT-4/Claude like pattern learning\n"
                    "• Win Rate: 80-85%+ target\n"
                    "• Learns from every result\n\n"
                    "🎨 Multiple Custom Break Messages\n"
                    "📝 Event Media System\n"
                    "🎯 Custom Messages for Every Event\n"
                    "⏱️ Adjustable Break Duration\n"
                    "⏯️ Per-Channel Prediction Control\n"
                    "⏰ Channel-Specific Time Windows (NEW!)\n"
                    "📎 Supports ANY file type\n"
                    "🎨 Stickers, GIFs, Photos, Videos, Documents\n\n"
                    "✅ Session start messages sent 5 minutes before each session!\n"
                    "✅ Win/Loss media now sends immediately!\n"
                    "Select an option below:",
                    reply_markup=self.get_keyboard('main')
                )
                
            elif data == 'stats':
                data_fetch = await self.fetch_live_data()
                if data_fetch and self.waiting_for_result:
                    await self.check_result_and_send_next(context, data_fetch)
                
                total_predictions = self.session_wins + self.session_losses
                session_win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0
                
                is_operational = True
                
                active_channels = [c for c in self.active_channels if self.is_channel_prediction_active(c)]
                paused_channels = [c for c in self.active_channels if not self.is_channel_prediction_active(c)]
                
                total_custom_messages = sum(len(msgs) for msgs in self.custom_break_messages.values() if isinstance(msgs, list))
                
                stats_text = f"""📊 Bot Statistics & AI Analysis

🤖 AI SYSTEM:
• AI Accuracy: {self.ai_accuracy:.2%}
• AI Predictions: {self.ai_total_predictions}
• AI Correct: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}
• Patterns Learned: {len(self.pattern_database)}

📈 PERFORMANCE:
• Session: {self.session_wins}W {self.session_losses}L
• Win Rate: {session_win_rate:.1f}%
• Consecutive Wins: {self.consecutive_wins}
• Consecutive Losses: {self.consecutive_losses}
• Last Result: {'🟢 WIN' if self.last_result_was_win else '🔴 LOSS'}

🌐 CHANNELS:
• Total Channels: {len(self.active_channels)}
• Active Predictions: {len(active_channels)}
• Paused Predictions: {len(paused_channels)}
• Custom Break Msgs: {total_custom_messages}

⏱️ SETTINGS:
• Break Duration: {self.custom_break_duration} minutes

⏰ CHANNEL TIMES:
"""
                for channel in self.active_channels:
                    if self.is_channel_prediction_active(channel):
                        schedule = self.get_session_schedule_text(channel)
                        stats_text += f"\n📢 {channel}:\n{schedule}"
                
                stats_text += f"""
🕒 SYSTEM:
• Status: {'🟢 ACTIVE' if is_operational else '🔴 SLEEP'}
• User Account: {'🟢 Active' if self.use_user_account and self.user_client_connected else '🔴 Inactive'}
• AI Status: {'🟢 Learning' if self.ai_total_predictions > 0 else '🟡 Training'}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('main'))
                
            elif data == 'templates_main_menu':
                await query.edit_message_text(
                    "📝 Templates Management\n\n"
                    "Edit all message templates with emoji support.\n"
                    "Use {placeholders} for dynamic content.\n\n"
                    "Available placeholders:\n"
                    "• {{session}} - Current session\n"
                    "• {{next_session}} - Next session\n"
                    "• {{register_link}} - Register link\n"
                    "• {{promo_text}} - Promotional text\n"
                    "• {{wins}} - Session wins\n"
                    "• {{losses}} - Session losses\n"
                    "• {{win_rate}} - Win rate percentage\n"
                    "• {{break_duration}} - Break duration\n"
                    "• {{period}} - Prediction period\n"
                    "• {{prediction}} - Prediction (BIG/SMALL)\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('templates_main_menu')
                )
                
            elif data == 'edit_all_templates':
                await query.edit_message_text(
                    "📄 Select template to edit for ALL channels:",
                    reply_markup=self.get_keyboard('edit_all_templates')
                )
                
            elif data == 'select_channel_templates':
                await query.edit_message_text(
                    "📢 Select channel to edit templates:",
                    reply_markup=self.get_keyboard('select_channel_templates')
                )
                
            elif data.startswith('channel_templates:'):
                channel_id = data.split(':', 1)[1]
                await query.edit_message_text(
                    f"📝 Templates for {channel_id}\n\n"
                    f"Select template to edit:",
                    reply_markup=self.get_keyboard('channel_templates', channel_id)
                )
                
            elif data.startswith('edit_template:'):
                parts = data.split(':')
                channel_id = parts[1]
                template_key = parts[2]
                
                if channel_id == 'all':
                    self.user_state[chat_id] = f'awaiting_template_all:{template_key}'
                    current_template = self.default_templates.get(template_key, '')
                    await query.edit_message_text(
                        f"📝 Edit Template for ALL Channels\n\n"
                        f"Template: {template_key}\n\n"
                        f"Current:\n{current_template[:200]}...\n\n"
                        f"Send new template (emojis will auto-convert):",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="templates_main_menu")]])
                    )
                else:
                    self.user_state[chat_id] = f'awaiting_template:{channel_id}:{template_key}'
                    current_template = self.get_channel_template(channel_id, template_key)
                    await query.edit_message_text(
                        f"📝 Edit Template for {channel_id}\n\n"
                        f"Template: {template_key}\n\n"
                        f"Current:\n{current_template[:200]}...\n\n"
                        f"Send new template (emojis will auto-convert):",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"channel_templates:{channel_id}")]])
                    )
            
            elif data == 'event_media_menu':
                await query.edit_message_text(
                    "📝 Event Media System\n\n"
                    "Set different media for each event type:\n"
                    "• Session Start\n"
                    "• Break\n"
                    "• Good Morning\n"
                    "• Good Night\n"
                    "• Win Result\n"
                    "• Loss Result\n\n"
                    "Supports multiple photos, videos, GIFs, stickers, documents.",
                    reply_markup=self.get_keyboard('event_media_menu')
                )

            elif data == 'subscription_menu':
                await query.edit_message_text(
                    "🧾 Subscriptions\n\n"
                    "Set or renew subscription days per channel.",
                    reply_markup=self.get_keyboard('subscription_menu')
                )

            elif data == 'select_channel_subscription':
                await query.edit_message_text(
                    "📋 Select Channel for Subscription:",
                    reply_markup=self.get_keyboard('select_channel_subscription')
                )

            elif data == 'view_all_subscriptions':
                if not self.channel_subscriptions:
                    await query.edit_message_text(
                        "❌ No subscriptions set yet.",
                        reply_markup=self.get_keyboard('subscription_menu')
                    )
                    return
                text = "🧾 Subscription Overview:\n\n"
                for ch, sub in self.channel_subscriptions.items():
                    text += f"• {ch}: expires {sub.get('expires_at','?')}\n"
                await query.edit_message_text(text, reply_markup=self.get_keyboard('subscription_menu'))

            elif data.startswith('subscription_channel:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_subscription_days:{channel_id}'
                await query.edit_message_text(
                    f"🧾 Set Subscription for {channel_id}\n\n"
                    f"Send number of days (e.g., 30):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="subscription_menu")]])
                )
                
            elif data == 'select_channel_event_media':
                await query.edit_message_text(
                    "📋 Select Channel for Event Media:",
                    reply_markup=self.get_keyboard('select_channel_event_media')
                )
                
            elif data == 'view_all_event_media':
                if not self.event_media:
                    await query.edit_message_text(
                        "❌ No event media configured!",
                        reply_markup=self.get_keyboard('event_media_menu')
                    )
                    return
                
                text = "👁️ Event Media Overview:\n\n"
                for channel_id, media_dict in self.event_media.items():
                    text += f"📢 {channel_id}:\n"
                    for event_type, media_list in media_dict.items():
                        if media_list:
                            event_name = self.message_types.get(event_type, event_type)
                            text += f"  • {event_name}: {len(media_list)} items\n"
                    text += "\n"
                
                await query.edit_message_text(
                    text,
                    reply_markup=self.get_keyboard('event_media_menu')
                )
                
            elif data.startswith('event_media_channel:'):
                channel_id = data.split(':', 1)[1]
                await query.edit_message_text(
                    f"📝 Event Media for {channel_id}\n\n"
                    f"Select event type to configure:",
                    reply_markup=self.get_keyboard('event_media_channel', channel_id)
                )
                
            elif data.startswith('event_media_type:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                await query.edit_message_text(
                    f"{self.message_types.get(event_type, event_type)} Media for {channel_id}",
                    reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                )
                
            elif data.startswith('add_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                self.user_state[chat_id] = f'awaiting_event_media:{channel_id}:{event_type}'
                
                await query.edit_message_text(
                    f"➕ Add {self.message_types.get(event_type, event_type)} Media for {channel_id}\n\n"
                    f"Send photos, videos, GIFs, stickers, or ANY file type.\n"
                    f"You can send multiple files.\n\n"
                    f"Send files now (multiple allowed):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"event_media_type:{channel_id}:{event_type}")]])
                )
                
            elif data.startswith('view_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                media_list = self.get_event_media(channel_id, event_type)
                if not media_list:
                    await query.edit_message_text(
                        f"❌ No {self.message_types.get(event_type, event_type)} media for {channel_id}",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                    return
                
                text = f"👁️ {self.message_types.get(event_type, event_type)} Media for {channel_id}\n\n"
                for i, media in enumerate(media_list):
                    media_type = media.get('type', 'unknown')
                    file_name = media.get('file_name', f'File {i+1}')
                    text += f"{i+1}. {media_type.upper()}: {file_name}\n"
                
                buttons = []
                for i in range(len(media_list)):
                    buttons.append([InlineKeyboardButton(f"🗑️ Delete {i+1}", callback_data=f"delete_event_media:{channel_id}:{event_type}:{i}")])
                buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"event_media_type:{channel_id}:{event_type}")])
                
                await query.edit_message_text(
                    text,
                    reply_markup=InlineKeyboardMarkup(buttons)
                )
                
            elif data.startswith('delete_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                index = int(parts[3])
                
                if self.delete_event_media(channel_id, event_type, index):
                    await query.edit_message_text(
                        f"✅ Deleted {self.message_types.get(event_type, event_type)} media #{index+1} for {channel_id}",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                    
            elif data.startswith('delete_all_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                if self.delete_event_media(channel_id, event_type):
                    await query.edit_message_text(
                        f"✅ All {self.message_types.get(event_type, event_type)} media deleted for {channel_id}",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
            
            elif data == 'custom_messages_menu':
                await query.edit_message_text(
                    "🎯 Custom Messages System - SIMPLIFIED\n\n"
                    "Create messages exactly as you want them to appear:\n"
                    "• Send a message with media + text combined\n"
                    "• Bot will store it exactly as sent\n"
                    "• Bot will forward it exactly the same way\n\n"
                    "No more multiple steps - send once, use forever!\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('custom_messages_menu')
                )
                
            elif data == 'select_channel_custom_messages':
                await query.edit_message_text(
                    "📋 Select Channel for Custom Messages:",
                    reply_markup=self.get_keyboard('select_channel_custom_messages')
                )
                
            elif data == 'view_all_custom_messages':
                if not self.custom_messages:
                    await query.edit_message_text(
                        "❌ No custom messages configured!",
                        reply_markup=self.get_keyboard('custom_messages_menu')
                    )
                    return
                
                text = "👁️ Custom Messages Overview:\n\n"
                for channel_id, msg_dict in self.custom_messages.items():
                    text += f"📢 {channel_id}:\n"
                    for msg_type, msg_list in msg_dict.items():
                        if msg_list:
                            type_name = self.message_types.get(msg_type, msg_type)
                            text += f"  • {type_name}: {len(msg_list)} messages\n"
                    text += "\n"
                
                await query.edit_message_text(
                    text,
                    reply_markup=self.get_keyboard('custom_messages_menu')
                )
                
            elif data == 'add_custom_message_start':
                await query.edit_message_text(
                    "➕ Add Custom Message\n\n"
                    "First, select which channel this message is for:",
                    reply_markup=self.get_keyboard('select_channel_custom_messages')
                )
                
            elif data.startswith('custom_messages_channel:'):
                channel_id = data.split(':', 1)[1]
                await query.edit_message_text(
                    f"🎯 Custom Messages for {channel_id}\n\n"
                    f"Select message type to configure:",
                    reply_markup=self.get_keyboard('custom_messages_channel', channel_id)
                )
                
            elif data.startswith('custom_messages_type:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                
                await query.edit_message_text(
                    f"{self.message_types.get(msg_type, msg_type)} Custom Messages for {channel_id}",
                    reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                )
                
            elif data.startswith('add_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2] if len(parts) > 2 else None
                
                if msg_type:
                    self.user_state[chat_id] = f'awaiting_custom_message:{channel_id}:{msg_type}'
                    await query.edit_message_text(
                        f"📝 Send the message EXACTLY as you want it to appear in channel.\n\n"
                        f"• You can send text only, media only, or media+text together\n"
                        f"• Bot will store it exactly as sent\n"
                        f"• Bot will forward it exactly the same way\n\n"
                        f"Type /cancel to abort.",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_messages_type:{channel_id}:{msg_type}")]])
                    )
                else:
                    await query.edit_message_text(
                        f"➕ Add Custom Message for {channel_id}\n\n"
                        f"Select message type:",
                        reply_markup=self.get_message_type_keyboard(channel_id)
                    )
                    
            elif data.startswith('view_custom_messages:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if not messages:
                    await query.edit_message_text(
                        f"❌ No {self.message_types.get(msg_type, msg_type)} messages for {channel_id}",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    return
                
                await query.edit_message_text(
                    f"👁️ {self.message_types.get(msg_type, msg_type)} Messages for {channel_id}",
                    reply_markup=self.get_keyboard('view_custom_messages', channel_id, event_type=msg_type)
                )
                
            elif data.startswith('edit_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                await query.edit_message_text(
                    f"✏️ Edit Message #{msg_index+1}",
                    reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                )
                
            elif data.startswith('preview_custom:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if not messages or msg_index >= len(messages):
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    return
                
                message_data = messages[msg_index]
                media_count = len(message_data.get('media_group', []))
                text_len = len(message_data.get('text', ''))
                send_order = message_data.get('send_order', 'text_first')
                
                preview_text = f"""👁️ Message Preview

• Media Items: {media_count}
• Text Length: {text_len} chars
• Send Order: {send_order}

Would you like to test send this message?"""
                
                await query.edit_message_text(
                    preview_text,
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🚀 Test Send", callback_data=f"test_send_custom:{channel_id}:{msg_type}:{msg_index}"),
                         InlineKeyboardButton("🔙 Back", callback_data=f"edit_custom_message:{channel_id}:{msg_type}:{msg_index}")]
                    ])
                )
                
            elif data.startswith('test_send_custom:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if messages and msg_index < len(messages):
                    await query.edit_message_text("🚀 Sending test message...")
                    await self.send_stored_message(context, channel_id, messages[msg_index])
                    await query.edit_message_text(
                        f"✅ Test message sent to {channel_id}!",
                        reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    
            elif data.startswith('change_custom_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                await query.edit_message_text(
                    f"🔄 Select Send Order for Message #{msg_index+1}:",
                    reply_markup=self.get_keyboard('send_order_menu', channel_id, event_type=msg_type, message_index=msg_index)
                )
                
            elif data.startswith('set_custom_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                send_order = parts[4]
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if messages and msg_index < len(messages):
                    messages[msg_index]['send_order'] = send_order
                    self.save_custom_messages()
                    await query.edit_message_text(
                        f"✅ Send order set to {send_order}!",
                        reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                    )
                    
            elif data.startswith('delete_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                if self.delete_custom_message(channel_id, msg_type, msg_index):
                    await query.edit_message_text(
                        f"✅ Custom message deleted!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    
            elif data.startswith('delete_all_custom_messages:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                
                if self.delete_custom_message(channel_id, msg_type):
                    await query.edit_message_text(
                        f"✅ All custom messages deleted for {self.message_types.get(msg_type, msg_type)}",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
            
            elif data == 'break_duration_menu':
                await query.edit_message_text(
                    f"⏱️ Break Duration Settings\n\n"
                    f"Current break duration: {self.custom_break_duration} minutes\n\n"
                    f"Set how long the break should last (1-120 minutes).\n"
                    f"This applies to all channels.\n\n"
                    f"Default: 60 minutes",
                    reply_markup=self.get_keyboard('break_duration_menu')
                )
                
            elif data == 'set_break_duration':
                self.user_state[chat_id] = 'awaiting_break_duration'
                await query.edit_message_text(
                    f"⏱️ Set Break Duration\n\n"
                    f"Current: {self.custom_break_duration} minutes\n\n"
                    f"Enter new break duration in minutes (1-120):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="break_duration_menu")]])
                )
            
            elif data == 'ai_management':
                await query.edit_message_text(
                    "🤖 AI Pattern Recognition Management\n\n"
                    "🎯 REAL AI Learning System\n"
                    "• Learns from every prediction\n"
                    "• Identifies winning patterns\n"
                    "• Improves accuracy over time\n\n"
                    "Current AI Accuracy: {:.2%}\n"
                    "Patterns Learned: {}\n\n"
                    "Select an option:".format(self.ai_accuracy, len(self.pattern_database)),
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'ai_stats':
                stats_text = f"""🤖 AI PATTERN RECOGNITION STATISTICS

📊 ACCURACY:
• Overall Accuracy: {self.ai_accuracy:.2%}
• Total Predictions: {self.ai_total_predictions}
• Correct Predictions: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}

🧠 PATTERN DATABASE:
• Patterns Learned: {len(self.pattern_database)}
• Pattern Types: {len(set(self.pattern_types.values()))}
• Recent Patterns: {len(self.recent_patterns)}

📈 PERFORMANCE TRENDS:
• Current Confidence: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Recent Success Rate: {(sum(1 for h in self.ai_prediction_history[-20:] if h.get('was_correct'))/20*100 if len(self.ai_prediction_history) >= 20 else 0):.1f}%
• Best Pattern Success: {max((p.get('success_rate', 0) for p in self.pattern_database.values()), default=0)*100:.1f}%

🔍 PATTERN ANALYSIS:
• Alternating Patterns: {self.pattern_types['alternating']}
• Streak Patterns: {self.pattern_types['streak']}
• Zigzag Patterns: {self.pattern_types['zigzag']}
• Cluster Patterns: {self.pattern_types['cluster']}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'view_patterns':
                if not self.pattern_database:
                    await query.edit_message_text(
                        "❌ No patterns learned yet!\n\n"
                        "AI needs more data to learn patterns.",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                patterns_text = "🔍 TOP WINNING PATTERNS:\n\n"
                
                sorted_patterns = sorted(
                    self.pattern_database.items(),
                    key=lambda x: x[1].get('success_rate', 0),
                    reverse=True
                )[:10]
                
                for i, (pattern_hash, pattern_data) in enumerate(sorted_patterns):
                    success_rate = pattern_data.get('success_rate', 0) * 100
                    occurrences = pattern_data.get('total_occurrences', 0)
                    last_seen = pattern_data.get('last_seen', 'Never')
                    
                    patterns_text += f"{i+1}. Success: {success_rate:.1f}% ({occurrences} times)\n"
                    patterns_text += f"   Last Seen: {last_seen[:16]}\n"
                    patterns_text += f"   Hash: {pattern_hash[:8]}...\n\n"
                
                patterns_text += f"Total Patterns: {len(self.pattern_database)}"
                
                await query.edit_message_text(patterns_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'retrain_ai':
                await query.edit_message_text("🔄 Retraining AI model...")
                self.retrain_ai_model()
                await query.edit_message_text(
                    f"✅ AI Model retrained!\n"
                    f"Learning Cycle: {self.ai_learning_cycles}\n"
                    f"Accuracy: {self.ai_accuracy:.2%}",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'clear_ai_data':
                confirm_keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ Yes, Clear All", callback_data="confirm_clear_ai_data"),
                     InlineKeyboardButton("❌ No, Keep Data", callback_data="ai_management")]
                ])
                await query.edit_message_text(
                    "⚠️ WARNING: Clear ALL AI Learning Data?\n\n"
                    "This will reset:\n"
                    "• All learned patterns\n"
                    "• AI accuracy history\n"
                    "• Pattern database\n\n"
                    "This action cannot be undone!",
                    reply_markup=confirm_keyboard
                )
                
            elif data == 'confirm_clear_ai_data':
                self.pattern_database = {}
                self.ai_correct_predictions = 0
                self.ai_total_predictions = 0
                self.ai_accuracy = 0.0
                self.ai_learning_cycles = 0
                self.pattern_history = []
                self.ai_prediction_history.clear()
                
                self.save_ai_model()
                
                await query.edit_message_text(
                    "✅ All AI data cleared!\n"
                    "AI will start learning from scratch.",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'pattern_analysis':
                if not self.ai_prediction_history:
                    await query.edit_message_text(
                        "❌ No prediction history yet!\n"
                        "AI needs to make more predictions.",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                recent_history = list(self.ai_prediction_history)[-20:]
                correct = sum(1 for h in recent_history if h.get('was_correct'))
                total = len(recent_history)
                recent_accuracy = (correct / total * 100) if total > 0 else 0
                
                pattern_types_count = Counter()
                for pattern_data in self.pattern_database.values():
                    pattern_str = pattern_data.get('pattern', '')
                    if len(pattern_str) >= 10:
                        pattern_type = self.identify_pattern_type([int(c) for c in pattern_str[:10]])
                        pattern_types_count[pattern_type] += 1
                
                analysis_text = f"""🎯 PATTERN ANALYSIS

📊 RECENT PERFORMANCE (Last 20):
• Accuracy: {recent_accuracy:.1f}%
• Correct: {correct}/{total}
• Win Streak: {self.consecutive_wins}
• Loss Streak: {self.consecutive_losses}

🧩 PATTERN DISTRIBUTION:
• Alternating: {pattern_types_count['alternating']}
• Streak: {pattern_types_count['streak']}
• Zigzag: {pattern_types_count['zigzag']}
• Cluster: {pattern_types_count['cluster']}
• Cycle: {pattern_types_count['cycle']}
• Random: {pattern_types_count['random']}

⚡ PREDICTION CONFIDENCE:
• Current: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Threshold: {self.ai_confidence_threshold*100:.0f}%
• AI Weight: {self.pattern_weights['ai_pattern']*100:.0f}%

🔮 RECOMMENDATION:
• {'✅ AI is performing well' if recent_accuracy > 65 else '⚠️ AI needs more training'}
• {'✅ Confidence is high' if getattr(self, 'last_ai_confidence', 0) > 0.7 else '⚠️ Low confidence predictions'}"""
                
                await query.edit_message_text(analysis_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'prediction_control':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!\n\nPlease add a channel first.",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "⏯️ Prediction Control\n\n"
                    "Control predictions for each channel individually:\n"
                    "• 🟢 = Predictions Active\n"
                    "• ⏸️ = Predictions Paused\n\n"
                    "Select channel to toggle:",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data.startswith('toggle_channel_prediction:'):
                channel_id = data.split(':', 1)[1]
                new_status = self.toggle_channel_prediction(channel_id)
                status_text = "🟢 ACTIVATED" if new_status else "⏸️ PAUSED"
                
                await query.edit_message_text(
                    f"✅ Predictions {status_text} for {channel_id}",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data.startswith('toggle_single_channel_prediction:'):
                channel_id = data.split(':', 1)[1]
                new_status = self.toggle_channel_prediction(channel_id)
                status_text = "🟢 ACTIVATED" if new_status else "⏸️ PAUSED"
                
                await query.edit_message_text(
                    f"✅ Predictions {status_text} for {channel_id}",
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data == 'start_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, True)
                
                await query.edit_message_text(
                    "✅ All channel predictions STARTED!",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data == 'pause_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, False)
                
                await query.edit_message_text(
                    "⏸️ All channel predictions PAUSED!",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data == 'select_channel_config':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!\n\nPlease add a channel first.",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "📢 Select a channel to configure:",
                    reply_markup=self.get_keyboard('select_channel')
                )
                
            elif data.startswith('set_time_windows:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_time_windows:{channel_id}'
                
                current_windows = self.get_channel_time_windows(channel_id)
                current_text = self.get_session_schedule_text(channel_id)
                
                await query.edit_message_text(
                    f"⏰ Set Time Windows for {channel_id}\n\n"
                    f"Current Schedule:\n{current_text}\n\n"
                    f"Enter new schedule in format:\n"
                    f"start1-end1,start2-end2,start3-end3,start4-end4\n\n"
                    f"Example for Channel 1:\n"
                    f"10:00-11:00,13:00-14:00,17:00-18:00,20:00-21:00\n\n"
                    f"Example for Channel 2:\n"
                    f"09:30-10:30,13:30-14:30,16:30-17:30,20:30-21:30\n\n"
                    f"Send the time windows (24-hour format):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"channel_config:{channel_id}")]])
                )
                
            elif data == 'view_time_windows':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                
                text = "⏰ Channel Time Windows Overview:\n\n"
                for channel in self.active_channels:
                    schedule = self.get_session_schedule_text(channel)
                    status = "🟢 ACTIVE" if self.is_channel_in_time_window(channel) else "⏸️ BREAK"
                    text += f"📢 {channel}\n{schedule}Status: {status}\n\n"
                
                await query.edit_message_text(
                    text,
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
                )
                
            elif data == 'custom_break_menu':
                await query.edit_message_text(
                    "🎨 Multiple Custom Break Messages\n\n"
                    "Manage multiple custom messages that will be sent after break messages.\n"
                    "You can set different messages for each channel!\n\n"
                    "🎯 REAL AI PATTERN RECOGNITION ACTIVE\n"
                    "• Learns from every result\n"
                    "• Win Rate: 80-85%+ target\n\n"
                    "Features:\n"
                    "• Add multiple messages per channel\n"
                    "• Each message can have media + text\n"
                    "• Supports ANY file type\n"
                    "• Sequential or random mode",
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data == 'select_channel_custom_break':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('custom_break_menu')
                    )
                    return
                    
                await query.edit_message_text(
                    "📢 Select a channel to configure multiple custom break messages:",
                    reply_markup=self.get_keyboard('select_channel_custom_break')
                )
                
            elif data == 'view_all_custom_break':
                if not self.custom_break_messages:
                    await query.edit_message_text(
                        "❌ No custom break messages set!",
                        reply_markup=self.get_keyboard('custom_break_menu')
                    )
                    return
                
                messages_text = "👁️ All Custom Break Messages:\n\n"
                total_messages = 0
                for channel_id, messages in self.custom_break_messages.items():
                    if isinstance(messages, dict):
                        messages = [messages]
                    elif not isinstance(messages, list):
                        messages = []
                    
                    message_count = len(messages)
                    total_messages += message_count
                    channel_status = "✅" if self.get_channel_config(channel_id).get('custom_break_enabled', False) else "❌"
                    messages_text += f"• {channel_status} {channel_id}: {message_count} messages\n"
                    
                    for i, msg in enumerate(messages):
                        media_count = len(msg.get('media_group', []))
                        text_len = len(msg.get('text', ''))
                        messages_text += f"  └ Msg {i+1}: {media_count} media, {text_len} chars\n"
                
                messages_text += f"\n📊 Total: {total_messages} messages"
                
                await query.edit_message_text(
                    messages_text,
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data == 'toggle_break_mode':
                await query.edit_message_text(
                    "🔄 Toggle Break Message Mode\n\n"
                    "This affects all channels:\n"
                    "• Sequential: Send messages in order\n"
                    "• Random: Send random message each time\n\n"
                    "Note: You can also set mode per channel in channel settings.",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🔄 Sequential", callback_data="set_global_mode:sequential"),
                         InlineKeyboardButton("🎲 Random", callback_data="set_global_mode:random")],
                        [InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")]
                    ])
                )
                
            elif data.startswith('set_global_mode:'):
                mode = data.split(':', 1)[1]
                for channel_id in self.active_channels:
                    channel_config = self.get_channel_config(channel_id)
                    channel_config['custom_break_mode'] = mode
                    self.update_channel_config(channel_id, channel_config)
                
                await query.edit_message_text(
                    f"✅ All channels set to {mode} mode!",
                    reply_markup=self.get_keyboard('custom_break_menu')
                )
                
            elif data.startswith('channel_config:'):
                channel_id = data.split(':', 1)[1]
                channel_status = self.is_channel_prediction_active(channel_id)
                status_text = "🟢 ACTIVE" if channel_status else "⏸️ PAUSED"
                
                schedule = self.get_session_schedule_text(channel_id)
                current_time = self.get_ist_now().strftime("%H:%M")
                is_active = self.is_channel_in_time_window(channel_id)
                active_status = "🟢 ACTIVE" if is_active else "⏸️ BREAK"
                
                config_text = f"""⚙️ Configuration for {channel_id}

🎯 AI STATUS: {'🟢 ACTIVE' if self.ai_total_predictions > 50 else '🟡 TRAINING'}
AI Accuracy: {self.ai_accuracy:.2%}

Prediction Status: {status_text}
Current Time: {current_time}
Channel Status: {active_status}

{schedule}

Select what you want to configure:"""
                
                await query.edit_message_text(
                    config_text,
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data.startswith('custom_break_setup:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                messages = self.get_custom_break_messages(channel_id)
                
                status_text = "✅ Enabled" if channel_config.get('custom_break_enabled', False) else "❌ Disabled"
                message_count = len(messages)
                mode_text = "🔄 Sequential" if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else "🎲 Random"
                delay = channel_config.get('custom_break_delay', 5)
                
                setup_text = f"""🎨 Multiple Custom Break Messages for {channel_id}

🎯 REAL AI PATTERN RECOGNITION ACTIVE
• AI Accuracy: {self.ai_accuracy:.2%}
• Patterns Learned: {len(self.pattern_database)}

Status: {status_text}
Mode: {mode_text}
Total Messages: {message_count}
Delay: {delay} minutes after break

Options:"""
                
                await query.edit_message_text(
                    setup_text,
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('toggle_custom_break:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                current_status = channel_config.get('custom_break_enabled', False)
                channel_config['custom_break_enabled'] = not current_status
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['custom_break_enabled'] else "disabled"
                await query.edit_message_text(
                    f"✅ Custom break messages {status} for {channel_id}",
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('view_all_messages:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No custom break messages set for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                messages_text = f"📊 Custom Break Messages for {channel_id}\n\n"
                for i, msg in enumerate(messages):
                    media_count = len(msg.get('media_group', []))
                    text_content = msg.get('text', '')
                    text_len = len(text_content)
                    preview = text_content[:50] + "..." if len(text_content) > 50 else text_content
                    messages_text += f"📝 Message {i+1}:\n"
                    messages_text += f"• Media: {media_count} items\n"
                    messages_text += f"• Text: {text_len} chars\n"
                    messages_text += f"• Preview: {preview}\n\n"
                
                await query.edit_message_text(
                    messages_text,
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('add_custom_break:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_new_message_name:{channel_id}'
                
                await query.edit_message_text(
                    f"➕ Add New Custom Break Message for {channel_id}\n\n"
                    f"First, give this message a name (for easy identification):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_break_setup:{channel_id}")]])
                )
                
            elif data.startswith('edit_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if not message_data:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                message_name = message_data.get('name', f'Message {message_index+1}')
                media_count = len(message_data.get('media_group', []))
                text_len = len(message_data.get('text', ''))
                send_order = message_data.get('send_order', 'text_first')
                
                await query.edit_message_text(
                    f"✏️ Edit Message: {message_name}\n\n"
                    f"Media: {media_count} items\n"
                    f"Text: {text_len} characters\n"
                    f"Send Order: {send_order}\n\n"
                    f"🎯 AI Pattern Detection Active\n\n"
                    f"Select what to edit:",
                    reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                )
                
            elif data.startswith('edit_message_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                self.user_state[chat_id] = f'awaiting_edit_message_media:{channel_id}:{message_index}'
                
                await query.edit_message_text(
                    f"🖼️ Edit Media for Message {message_index+1}\n\n"
                    f"Send photos, videos, GIFs, stickers, or ANY file type to replace current media.\n"
                    f"You can send multiple files.\n\n"
                    f"Current media will be replaced!\n\n"
                    f"Send files now (multiple allowed):",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("✅ Keep Current Media", callback_data=f"edit_message:{channel_id}:{message_index}"),
                         InlineKeyboardButton("🗑️ Clear All Media", callback_data=f"clear_message_media:{channel_id}:{message_index}")],
                        [InlineKeyboardButton("🔙 Cancel", callback_data=f"edit_message:{channel_id}:{message_index}")]
                    ])
                )
                
            elif data.startswith('clear_message_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if message_data:
                    message_data['media_group'] = []
                    self.update_custom_break_message(channel_id, message_index, message_data)
                    await query.edit_message_text(
                        f"✅ All media cleared from message {message_index+1}",
                        reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('edit_message_text:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                self.user_state[chat_id] = f'awaiting_edit_message_text:{channel_id}:{message_index}'
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                current_text = message_data.get('text', '') if message_data else ''
                
                await query.edit_message_text(
                    f"📝 Edit Text for Message {message_index+1}\n\n"
                    f"Current text: {current_text[:100]}{'...' if len(current_text) > 100 else ''}\n\n"
                    f"Send the new text message:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"edit_message:{channel_id}:{message_index}")]])
                )
                
            elif data.startswith('edit_send_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                await query.edit_message_text(
                    f"🔄 Select Send Order for Message {message_index+1}:",
                    reply_markup=self.get_keyboard('send_order', channel_id, message_index)
                )
                
            elif data.startswith('set_send_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                send_order = parts[3]
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if message_data:
                    message_data['send_order'] = send_order
                    self.update_custom_break_message(channel_id, message_index, message_data)
                    await query.edit_message_text(
                        f"✅ Send order set to {send_order} for message {message_index+1}",
                        reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('preview_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if not message_data:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                message_name = message_data.get('name', f'Message {message_index+1}')
                media_count = len(message_data.get('media_group', []))
                text_content = message_data.get('text', '')
                text_len = len(text_content)
                send_order = message_data.get('send_order', 'text_first')
                
                preview_text = f"""👁️ Preview Message {message_index+1}: {message_name}

• Media Items: {media_count}
• Text Length: {text_len} characters
• Send Order: {send_order}

Text Preview (with premium emojis):
{self.format_custom_message_with_premium_emojis(text_content, channel_id)[:200]}{'...' if len(text_content) > 200 else ''}

Would you like to test send this message?"""
                
                await query.edit_message_text(
                    preview_text,
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🚀 Test Send", callback_data=f"test_send_message:{channel_id}:{message_index}"),
                         InlineKeyboardButton("🔙 Back", callback_data=f"edit_message:{channel_id}:{message_index}")]
                    ])
                )
                
            elif data.startswith('test_send_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                message_data = self.get_custom_break_message_by_index(channel_id, message_index)
                if message_data:
                    await query.edit_message_text("🚀 Sending test message...")
                    await self.send_stored_message(context, channel_id, message_data)
                    await query.edit_message_text(
                        f"✅ Test message sent to {channel_id}!\n"
                        f"🎯 Premium emojis were used if available.",
                        reply_markup=self.get_keyboard('edit_message', channel_id, message_index)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Message not found!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('select_message_edit:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No messages to edit!\n\nAdd a message first.",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                await query.edit_message_text(
                    f"✏️ Select Message to Edit for {channel_id}",
                    reply_markup=self.get_keyboard('select_message_edit', channel_id)
                )
                
            elif data.startswith('select_message_delete:'):
                channel_id = data.split(':', 1)[1]
                messages = self.get_custom_break_messages(channel_id)
                
                if not messages:
                    await query.edit_message_text(
                        f"❌ No messages to delete!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    return
                
                await query.edit_message_text(
                    f"🗑️ Delete Message for {channel_id}\n\n"
                    f"Select which message to delete:",
                    reply_markup=self.get_keyboard('select_message_delete', channel_id)
                )
                
            elif data.startswith('delete_message_confirm:'):
                parts = data.split(':')
                channel_id = parts[1]
                message_index = int(parts[2])
                
                if self.delete_custom_break_message(channel_id, message_index):
                    await query.edit_message_text(
                        f"✅ Message {message_index+1} deleted for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete message!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('delete_all_messages:'):
                channel_id = data.split(':', 1)[1]
                
                if self.delete_custom_break_message(channel_id):
                    await query.edit_message_text(
                        f"✅ ALL messages deleted for {channel_id}",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ No messages to delete!",
                        reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                    )
                    
            elif data.startswith('toggle_break_mode:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                current_mode = channel_config.get('custom_break_mode', 'sequential')
                new_mode = 'random' if current_mode == 'sequential' else 'sequential'
                channel_config['custom_break_mode'] = new_mode
                self.update_channel_config(channel_id, channel_config)
                
                mode_text = "Sequential" if new_mode == 'sequential' else "Random"
                await query.edit_message_text(
                    f"✅ Break message mode set to {mode_text} for {channel_id}",
                    reply_markup=self.get_keyboard('custom_break_setup', channel_id)
                )
                
            elif data.startswith('set_break_delay:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_break_delay:{channel_id}'
                
                current_delay = self.get_channel_config(channel_id).get('custom_break_delay', 5)
                
                await query.edit_message_text(
                    f"⏰ Set Custom Break Message Delay for {channel_id}\n\n"
                    f"Current delay: {current_delay} minutes\n\n"
                    f"Enter the delay in minutes (1-60) after break message when the custom messages should be sent:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_break_setup:{channel_id}")]])
                )
                
            elif data.startswith('links_setup:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                links_text = f"""🔗 Links Setup for {channel_id}

🎯 AI STATUS: Accuracy {self.ai_accuracy:.2%}

Current Configuration:
• Register Link: {channel_config['register_link']}
• Promo Text: {channel_config['promotional_text'][:50]}...

Select what to change:"""
                
                await query.edit_message_text(
                    links_text,
                    reply_markup=self.get_keyboard('links_setup', channel_id)
                )
                
            elif data.startswith('toggle_links:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                channel_config['show_links'] = not channel_config['show_links']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_links'] else "disabled"
                
                updated_config = self.get_channel_config(channel_id)
                
                show_links_text = "✅ Show Links" if updated_config['show_links'] else "❌ Hide Links"
                show_promo_text = "✅ Show Promo" if updated_config['show_promo'] else "❌ Hide Promo"
                
                toggle_menu = [
                    [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}"),
                     InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                    [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
                ]
                
                await query.edit_message_text(
                    f"✅ Links display {status} for {channel_id}",
                    reply_markup=InlineKeyboardMarkup(toggle_menu)
                )
                
            elif data.startswith('toggle_promo:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                channel_config['show_promo'] = not channel_config['show_promo']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_promo'] else "disabled"
                
                updated_config = self.get_channel_config(channel_id)
                
                show_links_text = "✅ Show Links" if updated_config['show_links'] else "❌ Hide Links"
                show_promo_text = "✅ Show Promo" if updated_config['show_promo'] else "❌ Hide Promo"
                
                toggle_menu = [
                    [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}"),
                     InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                    [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
                ]
                
                await query.edit_message_text(
                    f"✅ Promo text display {status} for {channel_id}",
                    reply_markup=InlineKeyboardMarkup(toggle_menu)
                )
                
            elif data.startswith('toggle_features:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                channel_status = self.is_channel_prediction_active(channel_id)
                
                features_text = f"""⚡ Feature Toggles for {channel_id}

🎯 AI STATUS:
• Accuracy: {self.ai_accuracy:.2%}
• Predictions: {self.ai_total_predictions}
• Learning: {'🟢 Active' if self.ai_total_predictions > 50 else '🟡 Training'}

Current Status:
• Predictions: {'🟢 Active' if channel_status else '⏸️ Paused'}
• Show Links: {'✅ Enabled' if channel_config['show_links'] else '❌ Disabled'}
• Show Promo Text: {'✅ Enabled' if channel_config['show_promo'] else '❌ Disabled'}
• Custom Break: {'✅ Enabled' if channel_config.get('custom_break_enabled', False) else '❌ Disabled'}
• Break Mode: {'🔄 Sequential' if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else '🎲 Random'}
• Premium Emojis: {'✅ Auto Convert' if self.use_user_account else '🔴 Manual Only'}
• AI Pattern Detection: ✅ Enabled

Toggle features on/off:"""
                
                await query.edit_message_text(
                    features_text,
                    reply_markup=self.get_keyboard('toggle_features', channel_id)
                )
                
            elif data.startswith('view_config:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                messages = self.get_custom_break_messages(channel_id)
                channel_status = self.is_channel_prediction_active(channel_id)
                schedule = self.get_session_schedule_text(channel_id)
                
                config_text = f"""👁️ Full Configuration for {channel_id}

🎯 AI SYSTEM:
• AI Accuracy: {self.ai_accuracy:.2%}
• AI Weight: {self.pattern_weights['ai_pattern']*100:.0f}%
• Patterns Learned: {len(self.pattern_database)}

Prediction Status: {'🟢 ACTIVE' if channel_status else '⏸️ PAUSED'}

⏰ TIME WINDOWS:
{schedule}

Links:
• Register Link: {channel_config['register_link']}
• Promo Text: {channel_config['promotional_text']}

Features:
• Show Links: {'✅ Yes' if channel_config['show_links'] else '❌ No'}
• Show Promo: {'✅ Yes' if channel_config['show_promo'] else '❌ No'}
• Custom Break: {'✅ Enabled' if channel_config.get('custom_break_enabled', False) else '❌ Disabled'}
• Break Mode: {'🔄 Sequential' if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else '🎲 Random'}
• Break Delay: {channel_config.get('custom_break_delay', 5)} minutes
• Premium Emojis: {'✅ Auto Convert Enabled' if self.use_user_account else '❌ Manual Only'}
• AI Pattern Detection: ✅ Enabled

Custom Break Messages: {len(messages)} messages

Templates Preview:
• Prediction: {self.get_channel_template(channel_id, 'prediction_header')[:50]}...
• Morning: {self.get_channel_template(channel_id, 'good_morning')[:50]}...
• Night: {self.get_channel_template(channel_id, 'good_night')[:50]}...
• Break: {self.get_channel_template(channel_id, 'break_message')[:50]}..."""
                
                await query.edit_message_text(
                    config_text,
                    reply_markup=self.get_keyboard('channel_config', channel_id)
                )
                
            elif data.startswith('change_register_link:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_register_link:{channel_id}'
                
                channel_config = self.get_channel_config(channel_id)
                await query.edit_message_text(
                    f"✏️ Change Register Link for {channel_id}\n\n"
                    f"Current: {channel_config['register_link']}\n\n"
                    f"Please send the new register link:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data.startswith('change_promo_text:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_promo_text:{channel_id}'
                
                channel_config = self.get_channel_config(channel_id)
                await query.edit_message_text(
                    f"📢 Change Promo Text for {channel_id}\n\n"
                    f"Example: '🎁 Register now and get DAILY FREE GIFT CODE! 🎁'\n\n"
                    f"Current: {channel_config['promotional_text']}\n\n"
                    f"Please send the new promotional text:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data == 'add_channel':
                self.user_state[chat_id] = 'awaiting_add_channel'
                await query.edit_message_text(
                    "➕ Add New Channel\n\n"
                    "Send channel username (@mychannel) or numeric ID (-1001234567890):\n\n"
                    "For user account: Bot/User must be member\n\n"
                    "Channel 1 will get: 10:00-11:00, 13:00-14:00, 17:00-18:00, 20:00-21:00\n"
                    "Channel 2 will get: 09:30-10:30, 13:30-14:30, 16:30-17:30, 20:30-21:30",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="main_menu")]])
                )
                
            elif data == 'remove_channel':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels to remove!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "🗑️ Remove Channel\n\nSelect channel to remove:",
                    reply_markup=self.get_keyboard('remove_channel')
                )
                
            elif data.startswith('remove_channel_confirm:'):
                channel_id = data.split(':', 1)[1]

                candidates = {channel_id}
                if channel_id in self.username_to_id:
                    candidates.add(str(self.username_to_id[channel_id]))
                if channel_id.lstrip('-').isdigit():
                    chat_id_int = int(channel_id)
                    if chat_id_int in self.id_to_username:
                        candidates.add(self.id_to_username[chat_id_int])

                removed_any = False
                for cid in list(candidates):
                    if cid in self.active_channels:
                        self.active_channels.remove(cid)
                        removed_any = True
                    if cid in self.channel_configs:
                        del self.channel_configs[cid]
                    if cid in self.channel_prediction_status:
                        del self.channel_prediction_status[cid]
                    if cid in self.channel_time_windows:
                        del self.channel_time_windows[cid]
                    if cid in self.username_to_id:
                        del self.username_to_id[cid]
                    if cid in self.id_to_username:
                        del self.id_to_username[cid]
                    if cid in self.failed_channels:
                        self.failed_channels.remove(cid)
                    if cid in self.custom_break_messages:
                        del self.custom_break_messages[cid]
                    if cid in self.custom_break_schedules:
                        del self.custom_break_schedules[cid]
                    if cid in self.event_media:
                        del self.event_media[cid]
                    if cid in self.custom_messages:
                        del self.custom_messages[cid]

                if removed_any:
                    self.save_config()
                    self.save_custom_messages()
                    await query.edit_message_text(
                        f"✅ Channel {channel_id} removed successfully!",
                        reply_markup=self.get_keyboard('main')
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Channel {channel_id} not found!",
                        reply_markup=self.get_keyboard('main')
                    )
                
            elif data == 'broadcast_all':
                self.user_state[chat_id] = 'awaiting_broadcast_all'
                await query.edit_message_text(
                    "📢 Broadcast to All Active Channels\n\n"
                    "Send the message text now.\n"
                    "It will be sent to all active channels with subscription enabled.\n\n"
                    "Use /cancel to abort.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="main_menu")]])
                )

            elif data == 'advanced':
                await query.edit_message_text(
                    "🔄 Advanced Options",
                    reply_markup=self.get_keyboard('advanced')
                )
                
            elif data == 'reset_table':
                self.session_predictions = []
                self.consecutive_losses = 0
                self.consecutive_wins = 0
                self.session_wins = 0
                self.session_losses = 0
                self.predictions = {}
                self.safety_mode = False
                self.recovery_mode = False
                self.ultra_safe_mode = False
                self.waiting_for_win = False
                self.session_ended = False
                self.last_prediction_was_loss = False
                self.in_break_period = False
                self.night_mode = False
                self.morning_message_sent = False
                self.night_message_sent = False
                self.last_sent_period = None
                self.last_prediction_time = None
                self.current_prediction_period = None
                self.current_prediction_choice = None
                self.waiting_for_result = False
                self.break_message_sent = False
                self.last_result_was_win = False
                self.big_small_history.clear()
                await query.edit_message_text(
                    "✅ Session reset complete!",
                    reply_markup=self.get_keyboard('advanced')
                )
                
            elif data == 'restart_bot':
                await query.edit_message_text("🔄 Restarting bot...")
                if self.user_app and self.use_user_account and self.user_client_connected:
                    await self.user_app.stop()
                raise SystemExit(1)
                
            elif data == 'noop':
                await query.answer()
                return

            elif data == 'resolve_peers':
                if self.use_user_account and self.user_app:
                    await query.edit_message_text("🔍 Resolving peers...")
                    await self.resolve_all_channels()
                    await query.edit_message_text(
                        "✅ Peers resolved successfully!",
                        reply_markup=self.get_keyboard('advanced')
                    )
                else:
                    await query.edit_message_text(
                        "❌ User account not active",
                        reply_markup=self.get_keyboard('advanced')
                    )
                
        except Exception as e:
            logging.error(f"Callback error: {e}")
            import traceback
            logging.error(traceback.format_exc())
            await query.edit_message_text(
                f"❌ Error: {str(e)}",
                reply_markup=self.get_keyboard('main')
            )

    async def handle_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user is None or update.effective_user.id not in self.config['admin_ids']:
            return
            
        chat_id = update.effective_chat.id
        message = update.message
        
        if chat_id not in self.user_state:
            return
            
        state = self.user_state[chat_id]
        text = message.text.strip() if message.text else ""
        
        if text == '/cancel':
            del self.user_state[chat_id]
            await message.reply_text("❌ Operation cancelled.")
            return
        
        if state == 'awaiting_broadcast_all' and text:
            sent = 0
            failed = 0
            for channel in self.active_channels:
                try:
                    if not self.is_channel_subscription_active(channel):
                        continue
                    ok = await self.send_message_with_retry(
                        context=context,
                        chat_id=channel,
                        text=text,
                        for_channel=True
                    )
                    if ok:
                        sent += 1
                    else:
                        failed += 1
                except Exception as e:
                    failed += 1

            await message.reply_text(
                f"✅ Broadcast complete\n"
                f"• Sent: {sent}\n"
                f"• Failed: {failed}"
            )
            del self.user_state[chat_id]
            return

        if state == 'awaiting_add_channel' and text:
            raw = text.strip()
            channel = raw

            if 't.me/' in raw:
                try:
                    channel = '@' + raw.split('t.me/', 1)[1].split('?', 1)[0].strip('/').strip()
                except Exception:
                    channel = raw

            is_username = channel.startswith('@')
            is_telegram_chat_id = channel.startswith('-100') and channel[1:].isdigit()
            
            if is_username or is_telegram_chat_id:
                if channel not in self.active_channels:
                    self.active_channels.append(channel)

                    if channel not in self.channel_configs:
                        self.channel_configs[channel] = {
                            'register_link': "https://bdgsg.com//#/register?invitationCode=5151329947",
                            'promotional_text': "{gift} Register now and get DAILY FREE GIFT CODE! {gift}",
                            'show_links': True,
                            'show_promo': True,
                            'templates': self.default_templates.copy(),
                            'custom_break_enabled': False,
                            'custom_break_delay': 5,
                            'custom_break_mode': 'sequential',
                            'prediction_start_hour': 7,
                            'prediction_end_hour': 24
                        }
                    
                    channel_index = len(self.active_channels) - 1
                    default_windows = self._get_default_windows_for_channel(channel_index)
                    self.channel_time_windows[channel] = default_windows

                    self.channel_prediction_status[channel] = True
                    self.failed_channels.discard(channel)
                    self.save_config()

                    if self.use_user_account and self.user_app:
                        try:
                            if channel.startswith('@'):
                                chat = await self.user_app.get_chat(channel)
                                self.username_to_id[channel] = chat.id
                                self.id_to_username[str(chat.id)] = channel
                            elif channel.lstrip('-').isdigit():
                                chat_id = int(channel)
                                chat = await self.user_app.get_chat(chat_id)
                                self.username_to_id[channel] = chat_id
                                self.id_to_username[str(chat_id)] = channel
                        except Exception as e:
                            logging.warning(f"⚠️ Resolve after add failed for {channel}: {e}")

                    self.user_state[chat_id] = f'awaiting_subscription_days:{channel}'
                    
                    schedule = self.get_session_schedule_text(channel)
                    await message.reply_text(
                        f"✅ Channel {channel} added and enabled.\n\n"
                        f"⏰ Time Windows set:\n{schedule}\n\n"
                        f"Now send subscription days for this channel (example: 30)."
                    )
                    return
                else:
                    await message.reply_text("❌ Channel already exists!")
            else:
                await message.reply_text("❌ Invalid format! Use @username, -100... ID, or t.me link\nExample days like 30 are only valid after channel is added.")
            del self.user_state[chat_id]

        elif state.startswith('awaiting_subscription_days:') and text:
            channel_id = state.split(':', 1)[1]
            try:
                days = int(text.strip())
                if days < 1 or days > 3650:
                    await message.reply_text("❌ Enter valid days between 1 and 3650")
                else:
                    sub = self.set_channel_subscription_days(channel_id, days)
                    await message.reply_text(
                        f"✅ Subscription set for {channel_id}\n"
                        f"Days: {days}\n"
                        f"Expires: {sub.get('expires_at')}"
                    )
            except Exception:
                await message.reply_text("❌ Invalid number. Send days like: 30")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_time_windows:') and text:
            channel_id = state.split(':', 1)[1]
            try:
                parts = text.split(',')
                windows = []
                for part in parts:
                    part = part.strip()
                    if '-' in part:
                        start, end = part.split('-')
                        start = start.strip()
                        end = end.strip()
                        if re.match(r'^([01]?[0-9]|2[0-3]):[0-5][0-9]$', start) and \
                           re.match(r'^([01]?[0-9]|2[0-3]):[0-5][0-9]$', end):
                            windows.append({
                                'start': start,
                                'end': end,
                                'name': f"{start}-{end}"
                            })
                
                if not windows:
                    await message.reply_text("❌ Invalid format! Example: 10:00-11:00,13:00-14:00,17:00-18:00,20:00-21:00")
                    return
                
                self.set_channel_time_windows(channel_id, windows)
                schedule = self.get_session_schedule_text(channel_id)
                await message.reply_text(
                    f"✅ Time windows updated for {channel_id}!\n\n{schedule}"
                )
                
            except Exception as e:
                await message.reply_text(f"❌ Error: {e}\n\nUse format: start1-end1,start2-end2,...")
            del self.user_state[chat_id]

        elif state == 'awaiting_break_duration' and text:
            try:
                duration = int(text)
                if 1 <= duration <= 120:
                    self.custom_break_duration = duration
                    self.save_config()
                    await message.reply_text(f"✅ Break duration set to {duration} minutes!")
                else:
                    await message.reply_text("❌ Duration must be between 1 and 120 minutes!")
            except ValueError:
                await message.reply_text("❌ Please enter a valid number!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_template:') and text:
            parts = state.split(':')
            channel_id = parts[1]
            template_key = parts[2]

            if channel_id not in self.active_channels:
                self.active_channels.append(channel_id)
                self.channel_prediction_status[channel_id] = True

            self.update_channel_config(channel_id, {
                'templates': {template_key: text}
            })
            self.save_config()
            await message.reply_text(f"✅ Template updated for {channel_id}!\n📝 Saved exactly as you sent.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_template_all:') and text:
            template_key = state.split(':', 1)[1]

            for channel_id in self.active_channels:
                self.update_channel_config(channel_id, {
                    'templates': {template_key: text}
                })

            await message.reply_text(f"✅ Template updated for ALL channels!\n📝 Saved exactly as you sent.")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_custom_message:') and (message.photo or message.video or message.document or message.animation or message.sticker or message.voice or text):
            parts = state.split(':')
            channel_id = parts[1]
            msg_type = parts[2]
            
            message_data = {
                'media_group': [],
                'text': '',
                'send_order': 'text_first',
                'timestamp': datetime.now().isoformat(),
                'source_chat_id': message.chat_id,
                'source_message_id': message.message_id
            }
            
            media_items = []
            
            if message.photo:
                media_items.append({
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.video:
                media_items.append({
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.animation:
                media_items.append({
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.sticker:
                media_items.append({
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })

            elif message.voice:
                media_items.append({
                    'type': 'voice',
                    'file_id': message.voice.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                
                media_items.append({
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                    
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif text:
                message_data['text'] = self.auto_detect_and_convert_message(text)
                
            message_data['media_group'] = media_items
            
            if media_items and message_data['text']:
                message_data['send_order'] = 'combined'
            elif media_items:
                message_data['send_order'] = 'media_first'
            else:
                message_data['send_order'] = 'text_first'
            
            index = self.add_custom_message_simple(channel_id, msg_type, message_data)
            
            emojis_converted = []
            if message_data['text']:
                for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                    if placeholder in message_data['text']:
                        emojis_converted.append(emoji)
            
            response = f"✅ Custom {self.message_types.get(msg_type, msg_type)} message stored!\n\n"
            response += f"• Media: {len(media_items)} items\n"
            response += f"• Text: {len(message_data['text'])} characters\n"
            response += f"• Send Order: {message_data['send_order']}\n"
            
            if emojis_converted:
                response += f"• Emojis converted: {', '.join(emojis_converted[:5])}"
                if len(emojis_converted) > 5:
                    response += f" and {len(emojis_converted) - 5} more"
            
            await message.reply_text(response)
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_event_media:') and (message.photo or message.video or message.document or message.animation or message.sticker or message.voice):
            parts = state.split(':')
            channel_id = parts[1]
            event_type = parts[2]
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.animation:
                media_item = {
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.sticker:
                media_item = {
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.voice:
                media_item = {
                    'type': 'voice',
                    'file_id': message.voice.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                
                media_item = {
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                index = self.add_event_media(channel_id, event_type, media_item)
                
                file_type = media_item.get('type', 'file')
                file_name = media_item.get('file_name', f"{file_type} {index+1}")
                
                await message.reply_text(
                    f"✅ {self.message_types.get(event_type, event_type)} {file_type.upper()} added: {file_name}\n"
                    f"Total files: {index+1}\n\n"
                    f"Send more files or type /done to finish."
                )
                
        elif state.startswith('awaiting_event_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            event_type = parts[2]
            
            media_list = self.get_event_media(channel_id, event_type)
            media_count = len(media_list)
            
            await message.reply_text(
                f"✅ Finished adding {self.message_types.get(event_type, event_type)} media!\n"
                f"Total media: {media_count}"
            )
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_new_message_name:') and text:
            channel_id = state.split(':', 1)[1]
            message_name = text
            
            new_message = {
                'name': message_name,
                'media_group': [],
                'text': '',
                'send_order': 'text_first'
            }
            
            message_index = self.add_custom_break_message(channel_id, new_message)
            
            self.user_state[chat_id] = f'awaiting_new_message_media:{channel_id}:{message_index}'
            
            await message.reply_text(
                f"✅ Message '{message_name}' created!\n\n"
                f"Now send photos, videos, GIFs, stickers, or ANY file type.\n"
                f"You can send multiple files, or send /skip to skip adding media."
            )
            
        elif state.startswith('awaiting_new_message_media:') and (message.photo or message.video or message.document or message.animation or message.sticker or message.voice or text == '/skip'):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            if text == '/skip':
                self.user_state[chat_id] = f'awaiting_new_message_text:{channel_id}:{message_index}'
                await message.reply_text(
                    f"⏭️ Skipped media.\n\n"
                    f"Now send the text message (or /skip for media only):"
                )
                return
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.animation:
                media_item = {
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.sticker:
                media_item = {
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.voice:
                media_item = {
                    'type': 'voice',
                    'file_id': message.voice.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                
                media_item = {
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                if 'media_group' not in message_data:
                    message_data['media_group'] = []
                
                message_data['media_group'].append(media_item)
                self.update_custom_break_message(channel_id, message_index, message_data)
                
                media_count = len(message_data['media_group'])
                file_type = media_item.get('type', 'file')
                file_name = media_item.get('file_name', f"{file_type} {media_count}")
                
                await message.reply_text(
                    f"✅ {file_type.upper()} added: {file_name}\n"
                    f"Total files: {media_count}\n\n"
                    f"Send more files or type /done to finish."
                )
            
        elif state.startswith('awaiting_new_message_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if message_data:
                media_count = len(message_data.get('media_group', []))
                
                self.user_state[chat_id] = f'awaiting_new_message_text:{channel_id}:{message_index}'
                
                await message.reply_text(
                    f"✅ Added {media_count} media items.\n\n"
                    f"Now send the text message (or /skip for media only):"
                )
            else:
                del self.user_state[chat_id]
            
        elif state.startswith('awaiting_new_message_text:') and (text or text == '/skip'):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            if text == '/skip':
                message_data['text'] = ''
                await message.reply_text(
                    f"✅ Message '{message_data.get('name', 'New Message')}' created (media only)!"
                )
            else:
                converted_text = self.auto_detect_and_convert_message(text)
                message_data['text'] = converted_text
                
                emojis_converted = []
                for emoji, placeholder in self.emoji_config['emoji_to_placeholder'].items():
                    if placeholder in converted_text:
                        emojis_converted.append(f"{emoji}")
                
                media_count = len(message_data.get('media_group', []))
                text_len = len(converted_text)
                
                response_text = f"✅ Message '{message_data.get('name', 'New Message')}' created!\n\n"
                response_text += f"• Media: {media_count} items\n"
                response_text += f"• Text: {text_len} characters\n"
                
                if emojis_converted:
                    response_text += f"• Emojis auto-converted: {', '.join(emojis_converted[:5])}"
                    if len(emojis_converted) > 5:
                        response_text += f" and {len(emojis_converted) - 5} more"
                
                await message.reply_text(response_text)
            
            if message_data.get('media_group') and message_data.get('text'):
                message_data['send_order'] = 'combined'
            elif message_data.get('media_group'):
                message_data['send_order'] = 'media_first'
            else:
                message_data['send_order'] = 'text_first'
                
            self.update_custom_break_message(channel_id, message_index, message_data)
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_edit_message_media:') and (message.photo or message.video or message.document or message.animation or message.sticker or message.voice):
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            message_data['media_group'] = []
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.animation:
                media_item = {
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.sticker:
                media_item = {
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.voice:
                media_item = {
                    'type': 'voice',
                    'file_id': message.voice.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                
                media_item = {
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                message_data['media_group'].append(media_item)
                self.update_custom_break_message(channel_id, message_index, message_data)
                
                media_count = len(message_data['media_group'])
                file_type = media_item.get('type', 'file')
                file_name = media_item.get('file_name', f"{file_type} {media_count}")
                
                await message.reply_text(
                    f"✅ {file_type.upper()} added: {file_name}\n"
                    f"Total files: {media_count}\n\n"
                    f"Send more files or type /done to finish."
                )
                
        elif state.startswith('awaiting_edit_message_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if message_data:
                media_count = len(message_data.get('media_group', []))
                await message.reply_text(
                    f"✅ Media updated for message {message_index+1}!\n"
                    f"Total media items: {media_count}"
                )
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_edit_message_text:') and text:
            parts = state.split(':')
            channel_id = parts[1]
            message_index = int(parts[2])
            
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                await message.reply_text("❌ Message not found!")
                del self.user_state[chat_id]
                return
            
            converted_text = self.auto_detect_and_convert_message(text)
            message_data['text'] = converted_text
            self.update_custom_break_message(channel_id, message_index, message_data)
            
            await message.reply_text(f"✅ Text updated for message {message_index+1}!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_break_delay:') and text:
            channel_id = state.split(':', 1)[1]
            
            try:
                delay = int(text)
                if 1 <= delay <= 60:
                    channel_config = self.get_channel_config(channel_id)
                    channel_config['custom_break_delay'] = delay
                    self.update_channel_config(channel_id, channel_config)
                    
                    await message.reply_text(f"✅ Custom break message delay set to {delay} minutes for {channel_id}!")
                else:
                    await message.reply_text("❌ Delay must be between 1 and 60 minutes!")
            except ValueError:
                await message.reply_text("❌ Please enter a valid number!")
                
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_register_link:') and text:
            channel_id = state.split(':', 1)[1]
            self.update_channel_config(channel_id, {'register_link': text})
            await message.reply_text(f"✅ Register link updated for {channel_id}!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_promo_text:') and text:
            channel_id = state.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {'promotional_text': converted_text})
            await message.reply_text(f"✅ Promotional text updated for {channel_id}!\n🎯 Emojis were auto-converted.")
            del self.user_state[chat_id]

    def get_message_type_keyboard(self, channel_id):
        buttons = []
        events = list(self.message_types.items())
        for i in range(0, len(events), 2):
            key1, name1 = events[i]
            if i+1 < len(events):
                key2, name2 = events[i+1]
                row = [
                    InlineKeyboardButton(name1, callback_data=f"add_custom_message:{channel_id}:{key1}"),
                    InlineKeyboardButton(name2, callback_data=f"add_custom_message:{channel_id}:{key2}")
                ]
            else:
                row = [InlineKeyboardButton(name1, callback_data=f"add_custom_message:{channel_id}:{key1}")]
            buttons.append(row)
        buttons.append([InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_messages_channel:{channel_id}")])
        return InlineKeyboardMarkup(buttons)

    # ==================== Keyboard Methods ====================
    def get_keyboard(self, keyboard_type, channel_id=None, message_index=None, result_type=None, event_type=None):
        
        main_menu = [
            [InlineKeyboardButton("📊 Stats & AI", callback_data="stats"), 
             InlineKeyboardButton("⚙️ Channel Settings", callback_data="select_channel_config")],
            [InlineKeyboardButton("⏯️ Prediction Control", callback_data="prediction_control"), 
             InlineKeyboardButton("➕ Add Channel", callback_data="add_channel")],
            [InlineKeyboardButton("🗑️ Remove Channel", callback_data="remove_channel"), 
             InlineKeyboardButton("🎨 Multiple Break Msgs", callback_data="custom_break_menu")],
            [InlineKeyboardButton("📝 Event Media", callback_data="event_media_menu"), 
             InlineKeyboardButton("🎯 Custom Messages", callback_data="custom_messages_menu")],
            [InlineKeyboardButton("⏱️ Break Duration", callback_data="break_duration_menu"), 
             InlineKeyboardButton("🧾 Subscriptions", callback_data="subscription_menu")],
            [InlineKeyboardButton("📝 Templates", callback_data="templates_main_menu"), 
             InlineKeyboardButton("🔄 Advanced", callback_data="advanced")],
            [InlineKeyboardButton("📢 Broadcast All", callback_data="broadcast_all")],
            [InlineKeyboardButton("⏰ View Time Windows", callback_data="view_time_windows")]
        ]
        
        if keyboard_type == 'templates_main_menu':
            templates_menu = [
                [InlineKeyboardButton("📄 All Templates", callback_data="edit_all_templates"),
                 InlineKeyboardButton("📊 By Channel", callback_data="select_channel_templates")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(templates_menu)
        
        if keyboard_type == 'edit_all_templates':
            templates_menu = [
                [InlineKeyboardButton("🌅 Good Morning", callback_data="edit_template:all:good_morning"),
                 InlineKeyboardButton("🌙 Good Night", callback_data="edit_template:all:good_night")],
                [InlineKeyboardButton("🎯 Single Prediction", callback_data="edit_template:all:single_prediction")],
                [InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")]
            ]
            return InlineKeyboardMarkup(templates_menu)
        
        if keyboard_type == 'ai_management':
            ai_menu = [
                [InlineKeyboardButton("📈 AI Statistics", callback_data="ai_stats"),
                 InlineKeyboardButton("🔍 View Patterns", callback_data="view_patterns")],
                [InlineKeyboardButton("🔄 Retrain AI", callback_data="retrain_ai"),
                 InlineKeyboardButton("🧹 Clear AI Data", callback_data="clear_ai_data")],
                [InlineKeyboardButton("🎯 Pattern Analysis", callback_data="pattern_analysis")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(ai_menu)
        
        if keyboard_type == 'break_duration_menu':
            duration_menu = [
                [InlineKeyboardButton("⏱️ Set Break Duration", callback_data="set_break_duration")],
                [InlineKeyboardButton(f"📊 Current: {self.custom_break_duration} min", callback_data="noop")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(duration_menu)
        
        if keyboard_type == 'event_media_menu':
            event_menu = [
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_event_media"),
                 InlineKeyboardButton("👁️ View All", callback_data="view_all_event_media")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(event_menu)

        if keyboard_type == 'subscription_menu':
            sub_menu = [
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_subscription")],
                [InlineKeyboardButton("👁️ View All", callback_data="view_all_subscriptions")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(sub_menu)
        
        if keyboard_type == 'custom_messages_menu':
            custom_menu = [
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_custom_messages"),
                 InlineKeyboardButton("👁️ View All", callback_data="view_all_custom_messages")],
                [InlineKeyboardButton("➕ Add Message", callback_data="add_custom_message_start")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(custom_menu)
        
        if keyboard_type == 'select_channel_templates':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"channel_templates:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"channel_templates:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'channel_templates' and channel_id:
            templates_menu = [
                [InlineKeyboardButton("🌅 Good Morning", callback_data=f"edit_template:{channel_id}:good_morning"),
                 InlineKeyboardButton("🌙 Good Night", callback_data=f"edit_template:{channel_id}:good_night")],
                [InlineKeyboardButton("🎯 Single Prediction", callback_data=f"edit_template:{channel_id}:single_prediction")],
                [InlineKeyboardButton("🔙 Back", callback_data="select_channel_templates")]
            ]
            return InlineKeyboardMarkup(templates_menu)
        
        if keyboard_type == 'select_channel_event_media':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="event_media_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"event_media_channel:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"event_media_channel:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="event_media_menu")])
            return InlineKeyboardMarkup(buttons)

        if keyboard_type == 'select_channel_subscription':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="subscription_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"subscription_channel:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"subscription_channel:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="subscription_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'event_media_channel' and channel_id:
            media_menu = []
            events = list(self.message_types.items())
            for i in range(0, len(events), 2):
                key1, name1 = events[i]
                if i+1 < len(events):
                    key2, name2 = events[i+1]
                    count1 = len(self.get_event_media(channel_id, key1))
                    count2 = len(self.get_event_media(channel_id, key2))
                    row = [
                        InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"event_media_type:{channel_id}:{key1}"),
                        InlineKeyboardButton(f"{name2} ({count2})", callback_data=f"event_media_type:{channel_id}:{key2}")
                    ]
                else:
                    count1 = len(self.get_event_media(channel_id, key1))
                    row = [InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"event_media_type:{channel_id}:{key1}")]
                media_menu.append(row)
            media_menu.append([InlineKeyboardButton("🔙 Back", callback_data="select_channel_event_media")])
            return InlineKeyboardMarkup(media_menu)
        
        if keyboard_type == 'event_media_type' and channel_id and event_type:
            media_list = self.get_event_media(channel_id, event_type)
            media_count = len(media_list)
            event_name = self.message_types.get(event_type, event_type)
            
            media_menu = [
                [InlineKeyboardButton(f"➕ Add {event_name} Media", callback_data=f"add_event_media:{channel_id}:{event_type}")],
                [InlineKeyboardButton(f"👁️ View All ({media_count})", callback_data=f"view_event_media:{channel_id}:{event_type}"),
                 InlineKeyboardButton(f"🗑️ Delete All", callback_data=f"delete_all_event_media:{channel_id}:{event_type}")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"event_media_channel:{channel_id}")]
            ]
            return InlineKeyboardMarkup(media_menu)
        
        if keyboard_type == 'select_channel_custom_messages':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="custom_messages_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                channel1 = self.active_channels[i]
                total1 = sum(len(self.get_custom_messages(channel1, t)) for t in self.message_types.keys())
                row.append(InlineKeyboardButton(f"📢 {channel1} ({total1})", callback_data=f"custom_messages_channel:{channel1}"))
                
                if i+1 < len(self.active_channels):
                    channel2 = self.active_channels[i+1]
                    total2 = sum(len(self.get_custom_messages(channel2, t)) for t in self.message_types.keys())
                    row.append(InlineKeyboardButton(f"📢 {channel2} ({total2})", callback_data=f"custom_messages_channel:{channel2}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="custom_messages_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'custom_messages_channel' and channel_id:
            custom_menu = []
            events = list(self.message_types.items())
            for i in range(0, len(events), 2):
                key1, name1 = events[i]
                count1 = len(self.get_custom_messages(channel_id, key1))
                
                if i+1 < len(events):
                    key2, name2 = events[i+1]
                    count2 = len(self.get_custom_messages(channel_id, key2))
                    row = [
                        InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"custom_messages_type:{channel_id}:{key1}"),
                        InlineKeyboardButton(f"{name2} ({count2})", callback_data=f"custom_messages_type:{channel_id}:{key2}")
                    ]
                else:
                    row = [InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"custom_messages_type:{channel_id}:{key1}")]
                custom_menu.append(row)
            custom_menu.append([InlineKeyboardButton("➕ Add Message", callback_data=f"add_custom_message:{channel_id}")])
            custom_menu.append([InlineKeyboardButton("🔙 Back", callback_data="select_channel_custom_messages")])
            return InlineKeyboardMarkup(custom_menu)
        
        if keyboard_type == 'custom_messages_type' and channel_id and event_type:
            messages = self.get_custom_messages(channel_id, event_type)
            msg_count = len(messages)
            event_name = self.message_types.get(event_type, event_type)
            
            msg_menu = [
                [InlineKeyboardButton(f"➕ Add {event_name} Message", callback_data=f"add_custom_message:{channel_id}:{event_type}")],
                [InlineKeyboardButton(f"👁️ View All ({msg_count})", callback_data=f"view_custom_messages:{channel_id}:{event_type}"),
                 InlineKeyboardButton(f"🗑️ Delete All", callback_data=f"delete_all_custom_messages:{channel_id}:{event_type}")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"custom_messages_channel:{channel_id}")]
            ]
            return InlineKeyboardMarkup(msg_menu)
        
        if keyboard_type == 'view_custom_messages' and channel_id and event_type:
            messages = self.get_custom_messages(channel_id, event_type)
            if not messages:
                return self.get_keyboard('custom_messages_type', channel_id, event_type=event_type)
            
            buttons = []
            for i, msg in enumerate(messages):
                media_count = len(msg.get('media_group', []))
                text_len = len(msg.get('text', ''))
                send_order = msg.get('send_order', 'text_first')
                preview = f"Msg {i+1}: {media_count} media, {text_len} chars, {send_order}"
                buttons.append([InlineKeyboardButton(f"{preview[:40]}...", callback_data=f"edit_custom_message:{channel_id}:{event_type}:{i}")])
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"custom_messages_type:{channel_id}:{event_type}")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'edit_custom_message' and channel_id and event_type and message_index is not None:
            edit_menu = [
                [InlineKeyboardButton("👁️ Preview", callback_data=f"preview_custom:{channel_id}:{event_type}:{message_index}"),
                 InlineKeyboardButton("🚀 Send Now", callback_data=f"test_send_custom:{channel_id}:{event_type}:{message_index}")],
                [InlineKeyboardButton("🔄 Change Send Order", callback_data=f"change_custom_order:{channel_id}:{event_type}:{message_index}"),
                 InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_custom_message:{channel_id}:{event_type}:{message_index}")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"view_custom_messages:{channel_id}:{event_type}")]
            ]
            return InlineKeyboardMarkup(edit_menu)
        
        if keyboard_type == 'send_order_menu' and channel_id and event_type and message_index is not None:
            order_menu = [
                [InlineKeyboardButton("📝 Text First", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:text_first"),
                 InlineKeyboardButton("🖼️ Media First", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:media_first")],
                [InlineKeyboardButton("🎯 Combined", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:combined")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"edit_custom_message:{channel_id}:{event_type}:{message_index}")]
            ]
            return InlineKeyboardMarkup(order_menu)
        
        if keyboard_type == 'prediction_control':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                channel1 = self.active_channels[i]
                status1 = self.is_channel_prediction_active(channel1)
                status_text1 = "🟢" if status1 else "⏸️"
                row.append(InlineKeyboardButton(f"{status_text1} {channel1}", callback_data=f"toggle_channel_prediction:{channel1}"))
                
                if i+1 < len(self.active_channels):
                    channel2 = self.active_channels[i+1]
                    status2 = self.is_channel_prediction_active(channel2)
                    status_text2 = "🟢" if status2 else "⏸️"
                    row.append(InlineKeyboardButton(f"{status_text2} {channel2}", callback_data=f"toggle_channel_prediction:{channel2}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🟢 Start All", callback_data="start_all_predictions"),
                           InlineKeyboardButton("⏸️ Pause All", callback_data="pause_all_predictions")])
            buttons.append([InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'channel_config' and channel_id:
            channel_status = self.is_channel_prediction_active(channel_id)
            status_text = "⏸️ Pause Predictions" if channel_status else "▶️ Start Predictions"
            
            channel_config_menu = [
                [InlineKeyboardButton(status_text, callback_data=f"toggle_single_channel_prediction:{channel_id}")],
                [InlineKeyboardButton("⏰ Set Time Windows", callback_data=f"set_time_windows:{channel_id}")],
                [InlineKeyboardButton("🔗 Links Setup", callback_data=f"links_setup:{channel_id}"),
                 InlineKeyboardButton("📝 Templates", callback_data=f"channel_templates:{channel_id}")],
                [InlineKeyboardButton("🎨 Multiple Break Msgs", callback_data=f"custom_break_setup:{channel_id}"),
                 InlineKeyboardButton("📝 Event Media", callback_data=f"event_media_channel:{channel_id}")],
                [InlineKeyboardButton("🎯 Custom Messages", callback_data=f"custom_messages_channel:{channel_id}"),
                 InlineKeyboardButton("👁️ View Config", callback_data=f"view_config:{channel_id}")],
                [InlineKeyboardButton("⚡ Toggle Features", callback_data=f"toggle_features:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(channel_config_menu)
        
        elif keyboard_type == 'custom_break_menu':
            custom_break_menu = [
                [InlineKeyboardButton("📋 Manage by Channel", callback_data="select_channel_custom_break"),
                 InlineKeyboardButton("👁️ View All Messages", callback_data="view_all_custom_break")],
                [InlineKeyboardButton("🔄 Toggle Mode", callback_data="toggle_break_mode")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(custom_break_menu)
        
        elif keyboard_type == 'custom_break_setup' and channel_id:
            channel_config = self.get_channel_config(channel_id)
            custom_break_status = "✅ Enabled" if channel_config.get('custom_break_enabled', False) else "❌ Disabled"
            messages = self.get_custom_break_messages(channel_id)
            message_count = len(messages)
            mode_text = "🔄 Sequential" if channel_config.get('custom_break_mode', 'sequential') == 'sequential' else "🎲 Random"
            
            custom_break_setup_menu = [
                [InlineKeyboardButton(f"🔄 {custom_break_status}", callback_data=f"toggle_custom_break:{channel_id}"),
                 InlineKeyboardButton(f"📊 Msgs: {message_count}", callback_data=f"view_all_messages:{channel_id}")],
                [InlineKeyboardButton("➕ Add New", callback_data=f"add_custom_break:{channel_id}"),
                 InlineKeyboardButton("✏️ Edit", callback_data=f"select_message_edit:{channel_id}")],
                [InlineKeyboardButton("🗑️ Delete", callback_data=f"select_message_delete:{channel_id}"),
                 InlineKeyboardButton(f"🎲 Mode: {mode_text}", callback_data=f"toggle_break_mode:{channel_id}")],
                [InlineKeyboardButton("⏰ Set Delay", callback_data=f"set_break_delay:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(custom_break_setup_menu)
        
        elif keyboard_type == 'select_message_edit' and channel_id:
            messages = self.get_custom_break_messages(channel_id)
            buttons = []
            for i, msg in enumerate(messages):
                media_count = len(msg.get('media_group', []))
                text_len = len(msg.get('text', ''))
                buttons.append([InlineKeyboardButton(f"📝 Msg {i+1}: {media_count} media, {text_len} chars", callback_data=f"edit_message:{channel_id}:{i}")])
            buttons.append([InlineKeyboardButton("➕ Add New", callback_data=f"add_custom_break:{channel_id}"),
                           InlineKeyboardButton("🔙 Back", callback_data=f"custom_break_setup:{channel_id}")])
            return InlineKeyboardMarkup(buttons)
        
        elif keyboard_type == 'select_message_delete' and channel_id:
            messages = self.get_custom_break_messages(channel_id)
            buttons = []
            for i, msg in enumerate(messages):
                media_count = len(msg.get('media_group', []))
                text_len = len(msg.get('text', ''))
                buttons.append([InlineKeyboardButton(f"🗑️ Delete Msg {i+1}", callback_data=f"delete_message_confirm:{channel_id}:{i}")])
            buttons.append([InlineKeyboardButton("🗑️ Delete ALL", callback_data=f"delete_all_messages:{channel_id}"),
                           InlineKeyboardButton("🔙 Back", callback_data=f"custom_break_setup:{channel_id}")])
            return InlineKeyboardMarkup(buttons)
        
        elif keyboard_type == 'edit_message' and channel_id and message_index is not None:
            message_data = self.get_custom_break_message_by_index(channel_id, message_index)
            if not message_data:
                return self.get_keyboard('custom_break_setup', channel_id)
            
            media_count = len(message_data.get('media_group', []))
            text_len = len(message_data.get('text', ''))
            
            edit_message_menu = [
                [InlineKeyboardButton(f"🖼️ Edit Media ({media_count} items)", callback_data=f"edit_message_media:{channel_id}:{message_index}"),
                 InlineKeyboardButton(f"📝 Edit Text ({text_len} chars)", callback_data=f"edit_message_text:{channel_id}:{message_index}")],
                [InlineKeyboardButton("🔄 Send Order", callback_data=f"edit_send_order:{channel_id}:{message_index}"),
                 InlineKeyboardButton("👁️ Preview", callback_data=f"preview_message:{channel_id}:{message_index}")],
                [InlineKeyboardButton("🔙 Back to Messages", callback_data=f"select_message_edit:{channel_id}")]
            ]
            return InlineKeyboardMarkup(edit_message_menu)
        
        elif keyboard_type == 'send_order' and channel_id and message_index is not None:
            order_menu = [
                [InlineKeyboardButton("📝 Text First", callback_data=f"set_send_order:{channel_id}:{message_index}:text_first"),
                 InlineKeyboardButton("🖼️ Media First", callback_data=f"set_send_order:{channel_id}:{message_index}:media_first")],
                [InlineKeyboardButton("🎯 Combined", callback_data=f"set_send_order:{channel_id}:{message_index}:combined")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"edit_message:{channel_id}:{message_index}")]
            ]
            return InlineKeyboardMarkup(order_menu)
        
        elif keyboard_type == 'links_setup' and channel_id:
            links_menu = [
                [InlineKeyboardButton("✏️ Change Register Link", callback_data=f"change_register_link:{channel_id}"),
                 InlineKeyboardButton("📢 Change Promo Text", callback_data=f"change_promo_text:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(links_menu)
        
        elif keyboard_type == 'toggle_features' and channel_id:
            channel_config = self.get_channel_config(channel_id)
            
            show_links_text = "✅ Show Links" if channel_config['show_links'] else "❌ Hide Links"
            show_promo_text = "✅ Show Promo" if channel_config['show_promo'] else "❌ Hide Promo"
            
            toggle_menu = [
                [InlineKeyboardButton(show_links_text, callback_data=f"toggle_links:{channel_id}"),
                 InlineKeyboardButton(show_promo_text, callback_data=f"toggle_promo:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ]
            return InlineKeyboardMarkup(toggle_menu)
        
        elif keyboard_type == 'advanced':
            advanced_menu = [
                [InlineKeyboardButton("🔄 Reset Session", callback_data="reset_table"),
                 InlineKeyboardButton("🔄 Restart Bot", callback_data="restart_bot")],
                [InlineKeyboardButton("🔍 Resolve Peers", callback_data="resolve_peers")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ]
            return InlineKeyboardMarkup(advanced_menu)
        
        elif keyboard_type == 'select_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"channel_config:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"channel_config:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        elif keyboard_type == 'select_channel_custom_break':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                channel1 = self.active_channels[i]
                messages1 = self.get_custom_break_messages(channel1)
                status1 = "✅" if self.get_channel_config(channel1).get('custom_break_enabled', False) else "❌"
                row.append(InlineKeyboardButton(f"{status1} {channel1} ({len(messages1)})", callback_data=f"custom_break_setup:{channel1}"))
                
                if i+1 < len(self.active_channels):
                    channel2 = self.active_channels[i+1]
                    messages2 = self.get_custom_break_messages(channel2)
                    status2 = "✅" if self.get_channel_config(channel2).get('custom_break_enabled', False) else "❌"
                    row.append(InlineKeyboardButton(f"{status2} {channel2} ({len(messages2)})", callback_data=f"custom_break_setup:{channel2}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="custom_break_menu")])
            return InlineKeyboardMarkup(buttons)
        
        elif keyboard_type == 'remove_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"❌ {self.active_channels[i]}", callback_data=f"remove_channel_confirm:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"❌ {self.active_channels[i+1]}", callback_data=f"remove_channel_confirm:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        return InlineKeyboardMarkup(main_menu)

    def get_current_session(self):
        """Legacy method - kept for compatibility"""
        utc_now = datetime.utcnow()
        ist_now = utc_now + timedelta(hours=5, minutes=30)
        
        current_hour = ist_now.hour
        current_minute = ist_now.minute
        
        if self.active_channels:
            first_channel = self.active_channels[0]
            is_active = self.is_channel_in_time_window(first_channel)
        else:
            is_active = False
        
        current_session = "ACTIVE" if is_active else "BREAK"
        next_session = self.get_next_session_time_for_channel(self.active_channels[0]) if self.active_channels else "10:00"
        
        return current_session, is_active, current_hour, current_minute, next_session, None

    def is_operational_time(self, current_hour, current_minute):
        return True

    async def main_loop(self, context: ContextTypes.DEFAULT_TYPE):
        logging.info("🚀 Bot started - REAL AI PATTERN RECOGNITION")
        logging.info("⏰ Channel-specific time windows enabled")
        logging.info("✅ Win/Loss media will send immediately on result")
        logging.info("✅ Session start messages sent 5 minutes before each session")
        
        if self.use_user_account:
            success = await self.initialize_user_client()
            if success:
                logging.info("✅ User account ready - Persistent connection active")
            else:
                logging.warning("⚠️ Using regular emojis")
        
        session_start_sent_for_channel = {}
        break_sent_for_channel = {}
        
        while True:
            try:
                if not self.active_channels:
                    await asyncio.sleep(60)
                    continue
                
                ist_now = self.get_ist_now()
                current_hour = ist_now.hour
                current_minute = ist_now.minute
                current_time = ist_now.strftime("%H:%M")
                
                # Check each channel's time windows
                for channel in self.active_channels:
                    if not self.is_channel_prediction_active(channel):
                        continue
                    
                    is_active = self.is_channel_in_time_window(channel)
                    
                    # NEW: Send session start message 5 minutes before session
                    if not is_active:
                        minutes_until_start = self.get_minutes_until_session_start(channel, ist_now)
                        
                        # Send session start 5 minutes before session begins
                        if 0 < minutes_until_start <= 5:
                            next_session_key = f"{channel}:prestart"
                            if next_session_key not in session_start_sent_for_channel:
                                await self.send_new_session_message(context, channel)
                                session_start_sent_for_channel[next_session_key] = True
                                logging.info(f"📢 Pre-session message sent for {channel} (starting in {minutes_until_start} min)")
                    
                    # Send session start message at beginning of each time window
                    if is_active:
                        current_window = self.get_current_session_name_for_channel(channel)
                        last_sent_key = f"{channel}:{current_window}"
                        
                        if last_sent_key not in session_start_sent_for_channel:
                            await self.send_new_session_message(context, channel)
                            session_start_sent_for_channel[last_sent_key] = True
                            break_sent_for_channel.pop(channel, None)
                            
                    # Send break message at end of time window
                    elif not is_active:
                        if current_hour < 8:
                            continue
                        if self.is_after_last_session_for_channel(channel, ist_now):
                            if break_sent_for_channel.get(channel) != 'night':
                                total_predictions = self.session_wins + self.session_losses
                                win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0
                                await self.send_event_message(context, channel, 'break', next_session='Tomorrow', break_duration=self.custom_break_duration)
                                await self.send_event_message(context, channel, 'good_night', wins=self.session_wins, losses=self.session_losses, win_rate=win_rate)
                                break_sent_for_channel[channel] = 'night'
                            continue
                        if channel not in break_sent_for_channel or break_sent_for_channel[channel] != current_time[:2]:
                            next_session = self.get_next_session_time_for_channel(channel)
                            await self.send_break_message_for_channel(context, channel, next_session)
                            break_sent_for_channel[channel] = current_time[:2]
                            session_start_sent_for_channel = {k: v for k, v in session_start_sent_for_channel.items() if not k.startswith(f"{channel}:")}
                
                # Morning and night messages (still apply globally)
                if current_hour == 8 and current_minute == 0 and not self.morning_message_sent:
                    await self.send_good_morning_message(context)
                    self.morning_message_sent = True
                    self.night_message_sent = False
                    self.session_ended = False
                    self.in_break_period = False
                    self.break_message_sent = False
                    self.waiting_for_result = False
                    self.last_result_was_win = False
                    self.waiting_for_win = False
                    self.session_wins = 0
                    self.session_losses = 0
                    self.consecutive_losses = 0
                    self.consecutive_wins = 0
                    self.big_small_history.clear()
                    session_start_sent_for_channel.clear()
                    break_sent_for_channel.clear()
                
                if current_hour == 0 and current_minute == 0 and not self.night_message_sent:
                    await self.send_good_night_message(context)
                    self.night_message_sent = True
                    self.morning_message_sent = False
                    self.session_ended = True
                    self.in_break_period = True
                
                # Process predictions for active channels
                active_channels_now = [c for c in self.active_channels if self.is_channel_prediction_active(c) and self.is_channel_in_time_window(c)]
                
                if active_channels_now:
                    data = await self.fetch_live_data()
                    
                    if not data:
                        await asyncio.sleep(10)
                        continue
                    
                    self.current_active_prediction_channels = active_channels_now
                    
                    if self.waiting_for_result:
                        await self.check_result_and_send_next(context, data)
                    else:
                        await self.send_first_prediction(context, data)
                
                if self.ai_total_predictions % 25 == 0 and self.ai_total_predictions > 0:
                    self.save_ai_model()
                
                await asyncio.sleep(10)
                
            except Exception as e:
                logging.error(f"❌ Loop error: {e}")
                import traceback
                logging.error(traceback.format_exc())
                await asyncio.sleep(30)

    async def shutdown(self):
        if self.user_client_keepalive_task:
            self.user_client_keepalive_task.cancel()
            try:
                await self.user_client_keepalive_task
            except:
                pass
        if self.user_app and self.use_user_account:
            try:
                await self.user_app.stop()
                self.user_client_connected = False
                logging.info("✅ User client stopped")
            except:
                pass

    def run(self):
        class _BotCtx:
            """Minimal context wrapper so main_loop can use context.bot.*"""
            def __init__(self, bot, bot_data):
                self.bot = bot
                self.bot_data = bot_data

        async def _post_init(application):
            _ctx = _BotCtx(application.bot, application.bot_data)
            application.bot_data["main_loop_task"] = asyncio.create_task(self.main_loop(_ctx))

        async def _post_shutdown(application):
            task = application.bot_data.get("main_loop_task")
            if task:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
                except Exception:
                    pass
            await self.shutdown()

        application = Application.builder().token(self.bot_token).concurrent_updates(True).post_init(_post_init).post_shutdown(_post_shutdown).build()
        
        application.add_handler(CommandHandler(["start", "admin"], self.start))
        application.add_handler(CallbackQueryHandler(self.handle_callback))
        application.add_handler(MessageHandler(filters.ALL, self.handle_message))
        
        logging.info("🚀 WinGo Bot Starting...")
        logging.info("🎯 REAL AI PATTERN RECOGNITION SYSTEM")
        logging.info("✅ USING SINGLE WORKING API URL")
        logging.info("✅ FIXED: Persistent Pyrogram connection")
        logging.info("✅ FIXED: Win/Loss media now sends immediately")
        logging.info("✅ NEW: Session start messages sent 5 minutes before each session")
        logging.info("⏰ Channel-specific time windows:")
        logging.info("   Channel 1: 10:00-11:00, 13:00-14:00, 17:00-18:00, 20:00-21:00")
        logging.info("   Channel 2: 09:30-10:30, 13:30-14:30, 16:30-17:30, 20:30-21:30")
        
        application.run_polling()

if __name__ == "__main__":
    BOT_TOKEN = "8643497947:AAFW_fCAe0VAaamPfSdhWkyfj7VWSEPnxZE"
    
    API_ID = 22748653
    API_HASH = "29bba513726e776d0b5fd55dfa893c5a"
    PHONE = "+919934755281"
    
    bot = WinGoBotEnhanced(BOT_TOKEN, api_id=API_ID, api_hash=API_HASH, phone=PHONE)
    bot.run()



